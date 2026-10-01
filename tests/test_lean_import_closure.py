import contextlib
import io
import importlib.util
import pathlib
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    'lean_import_closure', pathlib.Path(__file__).resolve().parents[1] / 'scripts/lean_import_closure.py')
closure = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = closure
SPEC.loader.exec_module(closure)


class TestImportHeaders(unittest.TestCase):
    def parse(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / 'Main.lean'
            path.write_text(text, encoding='utf-8')
            return closure.parse_imported_modules(path)

    def test_stops_at_commands_after_the_header(self):
        self.assertEqual(self.parse('import A\nimport B\nopen A\nnamespace Example\n'), ['A', 'B'])

    def test_handles_nested_and_line_comments_as_whitespace(self):
        self.assertEqual(self.parse('-- /- not a block comment\nimport/- why -/A\n'
                                    '/- nested /- block -/\n-/import B\n'), ['A', 'B'])

    def test_module_system_modifiers_and_escaped_names(self):
        self.assertEqual(self.parse('module\nprelude\npublic import A\nmeta import B\n'
                                    'import all C\nimport D.«name with spaces»\n'),
                         ['A', 'B', 'C', 'D.«name with spaces»'])

    def test_body_strings_do_not_create_imports(self):
        self.assertEqual(self.parse('import A\ndef text := " import B "\n'), ['A'])

    def test_closure_does_not_follow_namespace_as_an_import(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / 'Main.lean').write_text('import A\nopen Unused\n')
            (root / 'A.lean').write_text('import Mathlib.Data.Nat.Basic\n')
            (root / 'Unused.lean').write_text('')
            internal, external = closure.compute_import_closure(closure.build_repo_index(root), 'Main')
            self.assertEqual(internal, {'Main', 'A'})
            self.assertEqual(external, {'Mathlib.Data.Nat.Basic'})

    def test_check_rejects_orphans_and_respects_namespace_boundaries(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / 'Main.lean').write_text('import Core.Used\n')
            for module in ('Core.Used', 'Core.Orphan', 'Core.Legacy.Old', 'CoreOther'):
                path = root.joinpath(*module.split('.')).with_suffix('.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('')
            args = ['Main', '--repo', directory, '--check-prefix', 'Core',
                    '--exclude-prefix', 'Core.Legacy']
            errors = io.StringIO()
            with contextlib.redirect_stderr(errors):
                self.assertEqual(closure.main(args), 1)
            self.assertIn('Core.Orphan', errors.getvalue())
            self.assertNotIn('Core.Legacy', errors.getvalue())
            self.assertNotIn('CoreOther', errors.getvalue())
            (root / 'Core' / 'Used.lean').write_text('import Core.Orphan\n')
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(closure.main(args), 0)

    def test_repeated_imports_and_unicode_names(self):
        self.assertEqual(self.parse("import A\nimport A\nimport α.Name'\n"), ['A', "α.Name'"])

    def test_comment_markers_inside_escaped_name(self):
        self.assertEqual(self.parse('import A.«x--y/-z»\n'), ['A.«x--y/-z»'])

    def test_unterminated_header_comment_fails(self):
        with self.assertRaises(ValueError):
            self.parse('/- missing end')

    def test_body_is_not_lexed(self):
        self.assertEqual(self.parse('import A\ndef s := "/-"\n'), ['A'])

    def test_closure_resolves_escaped_module_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / 'Main.lean').write_text('import «name with spaces»\n')
            (root / 'name with spaces.lean').write_text('')
            internal, external = closure.compute_import_closure(closure.build_repo_index(root), 'Main')
            self.assertEqual(internal, {'Main', 'name with spaces'})
            self.assertEqual(external, set())
