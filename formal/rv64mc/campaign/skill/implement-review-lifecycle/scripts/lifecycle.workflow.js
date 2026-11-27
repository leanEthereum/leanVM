export const meta = {
  name: 'implement-review-lifecycle',
  description: 'Implement with a written defence, adversarially review the diff and the defence for defects and drift, golf, fix and re-review until clean',
  whenToUse: 'Run a spec from the implement-review-lifecycle skill (pass the spec as args)',
  phases: [
    { title: 'Implement' },
    { title: 'Golf' },
    { title: 'Review' },
    { title: 'Fix' },
    { title: 'Re-review' },
  ],
}

// ---- spec -------------------------------------------------------------------------------------
const S = (typeof args === 'string' ? JSON.parse(args) : args) || {}
const SKILL = S.skillDir || '~/.claude/skills/implement-review-lifecycle'
if (!S.task || !S.workdir || !S.runDir) throw new Error('spec needs task, workdir and runDir (see SKILL.md)')

const PROFILES = {
  'lean-proof': {
    pipeline: ['implement', 'golf', 'review-loop'], maxRounds: 3,
    stages: {
      implement: { model: 'opus', skills: ['lean4:prove', 'lean4:refactor', 'writing-lean-proofs'] },
      golf: { model: 'opus', skills: ['lean4:golf', 'lean4:refactor'] },
      review: { model: 'opus', count: 1, skills: ['adversarial-review', 'lean4:review'] },
      fix: { model: 'opus', skills: ['lean4:prove'] },
      rereview: { model: 'opus', count: 1, skills: ['adversarial-review'] },
    },
  },
  'lean-statement': {
    pipeline: ['implement', 'review-loop', 'golf', 'review-loop'], maxRounds: 4,
    stages: {
      implement: { model: 'opus', skills: ['lean-spec-authoring', 'lean4:prove'] },
      golf: { model: 'opus', skills: ['lean4:golf'] },
      review: { model: 'fable', count: 2, skills: ['adversarial-review', 'lean-spec-authoring'] },
      fix: { model: 'opus', skills: ['lean-spec-authoring'] },
      rereview: { model: 'fable', count: 2, skills: ['adversarial-review', 'lean-spec-authoring'] },
    },
  },
  'lean-build-speed': {
    pipeline: ['implement', 'review-loop', 'golf'], maxRounds: 2,
    stages: {
      implement: { model: 'opus', skills: ['lean4-build-speed', 'maintaining-lean-projects'] },
      golf: { model: 'opus', skills: ['lean4:golf'] },
      review: { model: 'opus', count: 1, skills: ['adversarial-review', 'lean4-build-speed'] },
      fix: { model: 'opus', skills: ['lean4-build-speed'] },
      rereview: { model: 'opus', count: 1 },
    },
  },
  'generic-code': {
    pipeline: ['implement', 'review-loop'], maxRounds: 3,
    stages: {
      implement: { model: 'sonnet' }, review: { model: 'opus', count: 1 },
      fix: { model: 'sonnet' }, rereview: { model: 'opus', count: 1 },
    },
  },
}
const P = PROFILES[S.profile] || PROFILES['generic-code']
const stage = (k) => Object.assign({}, (P.stages || {})[k] || {}, ((S.stages || {})[k]) || {})
const pipeline = S.pipeline || P.pipeline
const maxRounds = S.maxRounds || P.maxRounds || 3
const RUN = S.runDir
const base = S.base || 'HEAD'

// ---- prompt pieces ----------------------------------------------------------------------------
const skillsLine = (st) => (st.skills && st.skills.length)
  ? `Before anything else, load these skills with the Skill tool (a value that is a path: read that SKILL.md instead): ${st.skills.join(', ')}. If one is not available, say so in your report and continue.`
  : ''
const common = () => `TASK: ${S.task}
Working directory: ${S.workdir} (a git repository; work only there and in ${RUN}). Base commit for diffs: ${base}.
${S.owns ? `Files this work may change: ${S.owns.join(', ')}. Anything else needs a reason in the defence.` : ''}
${S.check ? `The check for changed code (run it after every change, quote its result): \`${S.check}\`` : ''}
${S.context || ''}
If the harness refuses a write, put that content in your final message instead; do not route around the refusal.
The lifecycle's rules are in ${SKILL}/SKILL.md; the defence format in ${SKILL}/references/defence.md; the review checklist and findings schema in ${SKILL}/references/review.md.`
const opts = (st, label, phase, schema) => {
  const o = { label, phase }
  if (st.model) o.model = st.model
  if (st.effort) o.effort = st.effort
  if (schema) o.schema = schema
  return o
}

const COMMIT = { type: 'object', properties: { head: { type: 'string' }, summary: { type: 'string' }, check: { type: 'string' } }, required: ['head', 'summary'] }
const FINDINGS = {
  type: 'object',
  properties: {
    clean: { type: 'boolean' }, summary: { type: 'string' },
    claims_checked: { type: 'array', items: { type: 'object', properties: { claim: { type: 'string' }, verdict: { type: 'string' }, how: { type: 'string' } }, required: ['claim', 'verdict'] } },
    findings: { type: 'array', items: { type: 'object', properties: {
      id: { type: 'string' }, severity: { type: 'string', enum: ['important', 'nit'] },
      kind: { type: 'string' }, location: { type: 'string' }, claim: { type: 'string' },
      issue: { type: 'string' }, evidence: { type: 'string' }, suggested_fix: { type: 'string' },
    }, required: ['id', 'severity', 'kind', 'issue'] } },
  },
  required: ['clean', 'summary', 'findings'],
}
const FIXED = {
  type: 'object',
  properties: {
    head: { type: 'string' }, summary: { type: 'string' },
    dispositions: { type: 'array', items: { type: 'object', properties: { id: { type: 'string' }, action: { type: 'string', enum: ['fixed', 'rebutted', 'deferred'] }, note: { type: 'string' } }, required: ['id', 'action', 'note'] } },
  },
  required: ['head', 'summary', 'dispositions'],
}

// ---- stages -----------------------------------------------------------------------------------
async function implement() {
  const st = stage('implement')
  return agent(`${skillsLine(st)}
You are the IMPLEMENTER.
${common()}
Do the task. Commit your work in the working directory (several commits are fine). Then write ${RUN}/DEFENCE.md following references/defence.md exactly: every decision a reviewer could disagree with, its reason and rejected alternative, the invariants you claim (written so they can be checked), the evidence (exact commands and results), what you did not do, and where you think the reviewer should look hardest. The defence is for the reviewer only: do not put it in code, comments or commit messages, and do not overstate; an accurate defence of a flawed change is worth more than a confident one.
Return the head commit, a summary, and the check result.`, opts(st, 'implement', 'Implement', COMMIT))
}

const MORE = { type: 'object', properties: { head: { type: 'string' }, summary: { type: 'string' }, check: { type: 'string' }, listDone: { type: 'boolean' } }, required: ['head', 'summary', 'listDone'] }
async function implementMore(head, pass) {
  const st = stage('implement')
  return agent(`${skillsLine(st)}
You are IMPLEMENTER pass ${pass}, continuing the same task after an earlier implementer (or several) ran out of budget. The work so far is ${base}..${head}, committed; its defence is ${RUN}/DEFENCE.md (read its "Not done" list and every "## Pass" section first).
${common()}
Continue the task's list in its order from the first item not done, skipping only items an earlier pass abandoned with a stated obstacle (retry one only if you see a concrete new route). Do not redo or restructure what earlier passes committed, except to fix a real defect you find in it (say so). Commit after each function. Then append a "## Pass ${pass}" section to ${RUN}/DEFENCE.md in the same format as the rest (decisions, claims, evidence, not done, where to look hardest), and update the header's head and the "Not done" list there by an entry in your section (do not rewrite earlier sections).
Return the head commit, a summary, the check result, and listDone: true if nothing worth doing remains on the task's list (everything done or abandoned with an obstacle), else false.`, opts(st, 'implement-' + pass, 'Implement', MORE))
}

async function golf(head) {
  const st = stage('golf')
  return agent(`${skillsLine(st)}
You are the GOLF pass.
${common()}
Simplify the change ${base}..${head} without changing what it means: shorter and more direct code or proofs, helpers where a pattern repeats, upstream lemmas over local ones. Touch only lines the change introduced or the files it owns. Commit. Append a "## Golf" section to ${RUN}/DEFENCE.md: one entry per change, saying why it preserves meaning and the check result. If you cannot say why a change is equivalent, do not make it.
Return the head commit, a summary and the check result.`, opts(st, 'golf', 'Golf', COMMIT))
}

async function reviewOnce(head, round, k, prev, lastReviewed) {
  const st = stage(prev ? 'rereview' : 'review')
  const range = prev ? `${lastReviewed}..${head} (new since the last review; the whole change is ${base}..${head})` : `${base}..${head}`
  const r = await agent(`${skillsLine(st)}
You are an ADVERSARIAL REVIEWER (round ${round}, reviewer ${k + 1}). Do not edit any file, and do not change the working tree's state (no git stash, checkout or reset there): see the base with \`git show <base>:<file>\` or a scratch copy under ${RUN}.
${common()}
Review the diff ${range} and the defence ${RUN}/DEFENCE.md (including its Golf and Amendments sections), following references/review.md: hunt defects in the code AND drift between the defence and the code (claims the diff does not bear out, changes the defence does not mention, evidence that does not reproduce, scope drift). Rerun cheap evidence yourself. Every finding needs a concrete failure scenario or evidence; speculative ones are nits. Report drift even when the code is right (a wrong title, a claim about something later removed, an overstated guarantee). Keep to the task's change: scripts and probes the implementer wrote are evidence, to be attacked only as far as a claim depends on them.
${prev ? `This is a RE-REVIEW. Previous findings and the fixer's dispositions:\n${JSON.stringify(prev, null, 1)}\nFor each: confirm the fix in the new diff, judge each rebuttal on its evidence, accept or reject each deferral; carry over unresolved ones with their original id. Then review the new diff and the amendment like a first review.` : ''}
Also write your findings as JSON to ${RUN}/review-round${round}-${k + 1}.json. clean = true only if no important finding remains.`, opts(st, `${prev ? 're-review' : 'review'}${round}.${k + 1}`, prev ? 'Re-review' : 'Review', FINDINGS))
  return r
}

async function review(head, round, prev, lastReviewed) {
  const n = stage(prev ? 'rereview' : 'review').count || 1
  const rs = (await parallel(Array.from({ length: n }, (_, k) => () => reviewOnce(head, round, k, prev, lastReviewed)))).filter(Boolean)
  const findings = rs.flatMap((r, k) => (r.findings || []).map(f => Object.assign({}, f, { reviewer: k + 1 })))
  const clean = rs.length === n && rs.every(r => r.clean) && !findings.some(f => f.severity === 'important')
  return { clean, findings, summaries: rs.map(r => r.summary), claims: rs.flatMap(r => r.claims_checked || []) }
}

async function fix(head, round, findings, closeout) {
  const st = stage('fix')
  return agent(`${skillsLine(st)}
You are the ${closeout ? 'CLOSE-OUT pass (the review was clean; correct the defence for every drift finding and fix the cheap nits)' : 'FIX pass'} (round ${round}).
${common()}
The change so far is ${base}..${head}. Answer EVERY finding below: fix it (commit, run the check; to run the old code, use a scratch copy under ${RUN}, never a checkout in the working tree), rebut it with evidence if it is wrong (a reviewer can be wrong; say exactly why), or defer it with a reason and what it would take. Fix nits too when cheap. Then append "## Amendments, round ${round}" to ${RUN}/DEFENCE.md: per finding id, the disposition, what changed and the evidence; if a fix contradicts an earlier claim of the defence, say so explicitly. Never edit earlier entries.
Findings:
${JSON.stringify(findings, null, 1)}
Return the head commit, a summary and one disposition per finding id.`, opts(st, `fix${round}`, 'Fix', FIXED))
}

async function reviewLoop(head, log) {
  let r = await review(head, log.round + 1, null, null)
  log.round += 1
  log.rounds.push({ round: log.round, head, clean: r.clean, findings: r.findings, summaries: r.summaries, claims: r.claims })
  let lastReviewed = head
  let used = 1
  while (!r.clean && used < maxRounds) {
    const fx = await fix(head, log.round, r.findings)
    if (!fx) break
    log.rounds[log.rounds.length - 1].fix = fx
    head = fx.head || head
    const prev = r.findings.map(f => Object.assign({}, f, { disposition: (fx.dispositions || []).find(d => d.id === f.id) || null }))
    r = await review(head, log.round + 1, prev, lastReviewed)
    log.round += 1
    used += 1
    lastReviewed = head
    log.rounds.push({ round: log.round, head, clean: r.clean, findings: r.findings, summaries: r.summaries, claims: r.claims })
  }
  // out of rounds with findings left: stop and report them; a fix nobody reviews is not part of the lifecycle
  if (!r.clean) { log.stoppedAtMaxRounds = true; return head }
  // clean but with nits or drift: close out, so the defence ends up describing the code
  if (r.findings.length) {
    const fx = await fix(head, log.round, r.findings, true)
    if (fx) {
      log.rounds[log.rounds.length - 1].closeout = fx
      if (fx.head && fx.head !== head) {
        const prev = r.findings.map(f => Object.assign({}, f, { disposition: (fx.dispositions || []).find(d => d.id === f.id) || null }))
        const rr = await review(fx.head, log.round + 1, prev, head)
        log.round += 1
        log.rounds.push({ round: log.round, head: fx.head, clean: rr.clean, findings: rr.findings, summaries: rr.summaries, claims: rr.claims, afterCloseout: true })
        head = fx.head
      }
    }
  }
  return head
}

// ---- run --------------------------------------------------------------------------------------
const log = { spec: { profile: S.profile || 'generic-code', pipeline, maxRounds }, round: 0, rounds: [], stages: [] }
let head = base
for (const step of pipeline) {
  if (step === 'implement') {
    const r = await implement()
    if (!r) throw new Error('implement stage returned nothing')
    head = r.head; log.stages.push({ step, head, summary: r.summary, check: r.check })
    for (let pass = 2; pass <= (S.implementPasses || 1); pass++) {
      const m = await implementMore(head, pass)
      if (!m) break
      const moved = m.head !== head
      head = m.head; log.stages.push({ step: 'implement-' + pass, head, summary: m.summary, check: m.check })
      if (m.listDone || !moved) break
    }
  } else if (step === 'golf') {
    const r = await golf(head)
    if (r) { head = r.head; log.stages.push({ step, head, summary: r.summary, check: r.check }) }
  } else if (step === 'review-loop') {
    head = await reviewLoop(head, log)
    log.stages.push({ step, head, rounds: log.round })
  } else {
    log.stages.push({ step, skipped: 'unknown stage' })
  }
}
const last = log.rounds[log.rounds.length - 1]
log.final = { head, clean: last ? last.clean : null, open: last ? last.findings.filter(f => f.severity === 'important') : [], defence: `${RUN}/DEFENCE.md` }
return log
