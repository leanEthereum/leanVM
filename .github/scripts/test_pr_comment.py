import unittest

import pr_comment


class BenchmarkPresentationTests(unittest.TestCase):
    def report(self, cases):
        return pr_comment.bench(
            [{
                "base": "a" * 40,
                "testbed": "arm64",
                "cpu": "Neoverse-V2",
                "runs": [
                    {"round": 1, "side": side, "results": {
                        name: {measure: {"value": pair[index]} for measure, pair in measures.items()}
                        for name, measures in cases.items()
                    }}
                    for index, side in enumerate(("base", "head"))
                ],
            }],
            "b" * 40,
        ).split("<details><summary>Every result</summary>")[0]

    def sections(self, report):
        sections = {}
        current = None
        for line in report.splitlines():
            if line.startswith("#### "):
                current = sections.setdefault(line[5:], [])
            elif current is not None and line.startswith("| "):
                current.append([cell.strip() for cell in line.strip("|").split("|")])
        return sections

    def test_thread_variants_remain_distinct_and_sort_numerically(self):
        cases = {
            f"leanxmss-100-{count}thread": {"latency": (1e9, count * 2e9)}
            for count in (16, 8, 1, 4)
        }
        cases["leanxmss-100"] = {"latency": (1e9, 3e9)}
        rows = self.sections(self.report(cases))["leanXMSS"][1:]
        self.assertEqual([row[:3] for row in rows], [
            ["leanxmss-100", count, "arm64"] for count in ("default", "1", "4", "8", "16")
        ])
        self.assertEqual([row[-2] for row in rows], ["3.00 s", "2.00 s", "8.00 s", "16.00 s", "32.00 s"])

    def test_program_families_do_not_mix_or_drop_aggregation_levels(self):
        names = [
            "falcon-7-16thread",
            "leansphincs-26-16thread",
            "leanxmss-100-16thread",
            "aggregate-leanxmss-100-2to1-16thread-first",
            "aggregate-leanxmss-100-2to1-16thread-node",
            "future-program-16thread",
        ]
        sections = self.sections(self.report({name: {"latency": (1e9, 2e9)} for name in names}))
        self.assertEqual({title: [row[0] for row in rows[1:]] for title, rows in sections.items()}, {
            "Falcon": ["falcon-7"],
            "leanSPHINCS": ["leansphincs-26"],
            "leanXMSS": ["aggregate-leanxmss-100-2to1-first", "aggregate-leanxmss-100-2to1-node", "leanxmss-100"],
            "Other benchmarks": ["future-program"],
        })

    def test_hash_families_of_both_branches(self):
        names = ["hash-50000-16thread", "blake2s-batch-16thread", "flock-class-batch-16thread", "keccak-hash-batch-262144"]
        sections = self.sections(self.report({name: {"latency": (1e9, 2e9)} for name in names}))
        self.assertEqual({title: [row[0] for row in rows[1:]] for title, rows in sections.items()}, {
            "Hash chains": ["hash-50000"],
            "BLAKE2s": ["blake2s-batch"],
            "Flock": ["flock-class-batch"],
            "Keccak GKR": ["keccak-hash-batch-262144"],
        })

    def test_stage_only_changes_stay_attached_to_full_thread_identity(self):
        report = self.report({
            "leanxmss-100-4thread": {"latency": (10e9, 10e9), "stage.commit": (1e9, 2e9)},
            "leanxmss-100-16thread": {"latency": (20e9, 20e9), "stage.commit": (3e9, 4e9)},
        })
        rows = self.sections(report)["leanXMSS"][1:]
        self.assertEqual([(rows[index][1], rows[index][-2], rows[index + 1][-2]) for index in (0, 2)], [
            ("4", "10.00 s", "2.00 s"), ("16", "20.00 s", "4.00 s"),
        ])
        self.assertTrue(all(len(row) == len(rows[0]) for row in rows))

    def test_unnamed_default_is_not_compared_with_new_named_configuration(self):
        report = pr_comment.bench([{
            "base": "a" * 40, "testbed": "x86-64", "cpu": "Xeon",
            "runs": [
                {"round": 1, "side": "base", "results": {"falcon-7": {"latency": {"value": 1e9}}}},
                {"round": 1, "side": "head", "results": {"falcon-7-16thread": {"latency": {"value": 2e9}}}},
            ],
        }], "b" * 40).split("<details><summary>Every result</summary>")[0]
        rows = self.sections(report)["Falcon"][1:]
        self.assertEqual([(row[1], row[-3:]) for row in rows], [
            ("default", ["1.00 s", "none", "removed"]),
            ("16", ["none", "2.00 s", "new"]),
        ])

    def test_heap_bytes_and_allocation_counts_are_not_times(self):
        report = self.report({"falcon-7-16thread": {
            "heap-peak": (2**20, 2 * 2**20),
            "allocations": (1000, 2000),
        }})
        rows = self.sections(report)["Falcon"][1:]
        self.assertEqual({tuple(row[-3:-1]) for row in rows}, {
            ("1.00 MiB", "2.00 MiB"),
            ("1,000", "2,000"),
        })


if __name__ == "__main__":
    unittest.main()
