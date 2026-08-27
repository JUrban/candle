import unittest

import check_flyspeck_normalized_identity as identity_scan


class NormalizedIdentityScanTests(unittest.TestCase):
    def test_masks_comments_strings_and_hol_quotations(self):
        source = '''
(* a == b *)
let message = "a != b";;
let theorem = `p ==> q`;;
let value = x = y;;
'''
        self.assertEqual(identity_scan.executable_physical_operators(source), [])

    def test_reports_infix_and_operator_reference(self):
        source = "let p = x == y;;\nlet q = List.filter ((!=) x) xs;;\n"
        self.assertEqual(
            identity_scan.executable_physical_operators(source),
            [(1, "=="), (2, "!=")],
        )


if __name__ == "__main__":
    unittest.main()
