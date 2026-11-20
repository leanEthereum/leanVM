"""Fail if a Windows wheel's extension module needs the Visual C++ runtime DLLs.

.cargo/config.toml links the C runtime statically (+crt-static) for x86_64-pc-windows-msvc, so
the extension must load on a machine without the Visual C++ redistributable.

Usage: python check-windows-imports.py WHEEL...  (requires `pip install pefile`)
"""

import sys
import zipfile

import pefile

# The dynamic MSVC runtime: the redistributable's DLLs and the UCRT forwarders.
DYNAMIC_CRT_PREFIXES = ("vcruntime", "msvcp", "concrt", "ucrtbase", "api-ms-win-crt-")


def main(wheels: list[str]) -> int:
    if not wheels:
        print("usage: check-windows-imports.py WHEEL...", file=sys.stderr)
        return 2
    failed = False
    checked = 0
    for wheel in wheels:
        with zipfile.ZipFile(wheel) as archive:
            for member in archive.namelist():
                if not member.endswith(".pyd"):
                    continue
                checked += 1
                pe = pefile.PE(data=archive.read(member))
                if pe.FILE_HEADER.Machine != pefile.MACHINE_TYPE["IMAGE_FILE_MACHINE_AMD64"]:
                    print(f"{wheel}:{member}: not an x86-64 image")
                    failed = True
                dlls = sorted(entry.dll.decode() for entry in pe.DIRECTORY_ENTRY_IMPORT)
                print(f"{wheel}:{member} imports {', '.join(dlls)}")
                dynamic = [dll for dll in dlls if dll.lower().startswith(DYNAMIC_CRT_PREFIXES)]
                if dynamic:
                    print(f"  needs the dynamic C runtime: {', '.join(dynamic)}")
                    failed = True
    if checked == 0:
        print("no .pyd found in the given wheels")
        return 1
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
