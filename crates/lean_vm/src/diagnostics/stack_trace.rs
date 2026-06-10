use std::collections::{BTreeMap, BTreeSet};

use backend::ToUsize;
use backend::ansi::Colorize;

use crate::diagnostics::RunnerError;
use crate::execution::memory::MemoryAccess;
use crate::isa::Bytecode;
use crate::{CodeAddress, FunctionName, SourceLocation};

const MAX_STACK_FRAMES: usize = 256;

struct StackFrame {
    function: FunctionName,
    location: SourceLocation,
    pc: CodeAddress,
    fp: usize,
    return_pc: Option<CodeAddress>,
}

pub(crate) fn pretty_stack_trace<M: MemoryAccess>(
    bytecode: &Bytecode,
    error_pc: CodeAddress,
    error_fp: usize,
    memory: &M,
    error: &RunnerError,
) -> String {
    let mut out = String::new();
    let error_loc =
        error_source_location(error).or_else(|| bytecode.debug_info().pc_to_location.get(error_pc).copied());

    out.push_str(&format!("{}\n\n", "ERROR".red().bold()));

    if let Some(loc) = error_loc {
        let path = filepath(bytecode, loc.file_id);
        let (_, func) = find_function_for_location(loc, &bytecode.debug_info().function_locations);

        out.push_str(&format!(
            "  at {}:{} in {}\n\n",
            path,
            loc.line_number,
            func.blue().bold()
        ));

        // Source context
        if let Some(source) = bytecode.debug_info().source_code.get(&loc.file_id) {
            let lines: Vec<&str> = source.lines().collect();
            let err_line = loc.line_number.saturating_sub(1);
            let start = err_line.saturating_sub(3);
            let end = (err_line + 2).min(lines.len());

            for i in start..end {
                let content = lines.get(i).unwrap_or(&"");
                if i == err_line {
                    out.push_str(&format!(
                        "  {:>4} {} {}\n",
                        (i + 1).to_string().red().bold(),
                        "│".red(),
                        content
                    ));
                    let indent = content.len() - content.trim_start().len();
                    out.push_str(&format!(
                        "       {} {}{}\n",
                        "│".red(),
                        " ".repeat(indent),
                        "^".repeat(content.trim().len().max(1)).red()
                    ));
                } else {
                    out.push_str(&format!(
                        "  {:>4} {} {}\n",
                        (i + 1).to_string().dimmed(),
                        "│".dimmed(),
                        content.dimmed()
                    ));
                }
            }
        }
    }

    let (stack, truncated) = build_call_stack(bytecode, error_pc, error_fp, memory, error_loc);
    let visible_stack: Vec<_> = stack
        .iter()
        .filter(|frame| !is_generated_loop_function(&frame.function))
        .collect();
    if !visible_stack.is_empty() {
        out.push_str(&format!("\n{}\n\n", "CALL STACK".yellow().bold()));
        for (i, frame) in visible_stack.iter().enumerate() {
            let path = filepath(bytecode, frame.location.file_id);
            let marker = if i == 0 { "→".red().to_string() } else { " ".into() };
            let return_pc = frame.return_pc.map(|pc| format!(" return_pc={pc}")).unwrap_or_default();
            out.push_str(&format!(
                "  {} {} at {}:{} pc={} fp={}{}\n",
                marker,
                format!("{}()", frame.function).bold(),
                path.dimmed(),
                frame.location.line_number.to_string().dimmed(),
                frame.pc,
                frame.fp,
                return_pc,
            ));
        }
        if truncated {
            out.push_str(&format!(
                "    {}\n",
                format!("stack trace truncated after {MAX_STACK_FRAMES} frames").dimmed()
            ));
        }
    }

    out
}

fn build_call_stack<M: MemoryAccess>(
    bytecode: &Bytecode,
    error_pc: CodeAddress,
    error_fp: usize,
    memory: &M,
    error_loc: Option<SourceLocation>,
) -> (Vec<StackFrame>, bool) {
    let mut stack = Vec::new();
    let error_loc = error_loc.unwrap_or_else(unknown_location);
    let (_, current_function) = find_function_for_location(error_loc, &bytecode.debug_info().function_locations);
    stack.push(StackFrame {
        function: current_function,
        location: error_loc,
        pc: error_pc,
        fp: error_fp,
        return_pc: None,
    });

    let mut fp = error_fp;
    let mut seen_fps = BTreeSet::new();
    while stack.len() < MAX_STACK_FRAMES {
        if !seen_fps.insert(fp) {
            break;
        }

        let Ok(return_pc) = memory.get(fp).map(|value| value.to_usize()) else {
            break;
        };
        let Ok(saved_fp) = memory.get(fp + 1).map(|value| value.to_usize()) else {
            break;
        };

        let frame = if let Some(call_site) = bytecode.debug_info().call_sites_by_return_pc.get(&return_pc) {
            StackFrame {
                function: call_site.caller.clone(),
                location: call_site.location,
                pc: call_site.call_pc,
                fp: saved_fp,
                return_pc: Some(call_site.return_pc),
            }
        } else {
            let caller_pc = return_pc.saturating_sub(1);
            let loc = bytecode
                .debug_info()
                .pc_to_location
                .get(caller_pc)
                .copied()
                .unwrap_or_else(unknown_location);
            let (_, function) = find_function_for_location(loc, &bytecode.debug_info().function_locations);
            StackFrame {
                function,
                location: loc,
                pc: caller_pc,
                fp: saved_fp,
                return_pc: Some(return_pc),
            }
        };
        stack.push(frame);

        if saved_fp == fp {
            return (stack, false);
        }
        fp = saved_fp;
    }

    let truncated = stack.len() == MAX_STACK_FRAMES
        && !seen_fps.contains(&fp)
        && memory.get(fp).is_ok()
        && memory.get(fp + 1).is_ok();
    (stack, truncated)
}

fn is_generated_loop_function(function: &str) -> bool {
    function.starts_with("@loop_") || function.starts_with("@parallel_loop_")
}

fn error_source_location(error: &RunnerError) -> Option<SourceLocation> {
    match error {
        RunnerError::DebugAssertFailed(_, location) | RunnerError::RangeCheckWithTooBigRange { location, .. } => {
            Some(*location)
        }
        _ => None,
    }
}

pub(crate) fn find_function_for_location(
    loc: SourceLocation,
    func_locs: &BTreeMap<SourceLocation, FunctionName>,
) -> (SourceLocation, String) {
    func_locs
        .range(..=loc)
        .next_back()
        .map(|(l, f)| (*l, f.clone()))
        .unwrap_or((
            SourceLocation {
                file_id: 0,
                line_number: 0,
            },
            "<unknown>".into(),
        ))
}

fn unknown_location() -> SourceLocation {
    SourceLocation {
        file_id: 0,
        line_number: 0,
    }
}

fn filepath(bytecode: &Bytecode, file_id: usize) -> &str {
    bytecode
        .debug_info()
        .filepaths
        .get(&file_id)
        .map(|s| s.as_str())
        .unwrap_or("<unknown>")
}
