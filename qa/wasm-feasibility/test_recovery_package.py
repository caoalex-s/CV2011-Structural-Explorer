"""In-memory archive tests only; no local compiler or WASM execution."""
import io
import json
import tarfile
import unittest

from recovery_package import sha256, verify_package, validate_member_name


def fixture(members):
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode="w:gz") as archive:
        for name, data, kind in members:
            member = tarfile.TarInfo(name)
            member.type = kind
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
    stream.seek(0)
    return stream


class RecoveryPackageChecks(unittest.TestCase):
    def setUp(self):
        self.name = "files/.data/wasm-build/canonical/assets/checker.wasm"
        self.data = b"synthetic bytes, not an executable"
        self.index = {"format": 1, "members": {self.name: {
            "sha256": sha256(self.data), "bytes": len(self.data)}}}
        self.index_member = ("package-index.json", (json.dumps(self.index, indent=2) + "\n").encode(), tarfile.REGTYPE)
        self.file_member = (self.name, self.data, tarfile.REGTYPE)

    def test_hidden_named_member_is_retained_and_verified(self):
        self.assertTrue(verify_package(fixture([self.file_member, self.index_member]), self.index)["passed"])

    def test_missing_extra_duplicate_tampered_and_link_members_fail(self):
        cases = [[self.index_member], [self.file_member, self.index_member, ("extra", b"x", tarfile.REGTYPE)],
                 [self.file_member, self.file_member, self.index_member],
                 [(self.name, b"X" * len(self.data), tarfile.REGTYPE), self.index_member],
                 [(self.name, b"", tarfile.SYMTYPE), self.index_member]]
        for members in cases:
            with self.subTest(members=members), self.assertRaises(ValueError):
                verify_package(fixture(members), self.index)

    def test_traversal_and_absolute_names_fail(self):
        for name in ("../outside", "/absolute", "files/../outside", "files\\outside"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                validate_member_name(name)


if __name__ == "__main__":
    unittest.main()
