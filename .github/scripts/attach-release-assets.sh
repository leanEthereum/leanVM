#!/bin/sh
# Attach files to the GitHub release of $GITHUB_REF_NAME, skipping any already attached. A release's
# files are never replaced: Go's checksum database and Zig's package hashes pin the first upload.
set -eu

attached=$(gh release view "$GITHUB_REF_NAME" -R "$GITHUB_REPOSITORY" --json assets -q '.assets[].name')
for file in "$@"; do
    name=$(basename -- "$file")
    if printf '%s\n' "$attached" | grep -qxF -- "$name"; then
        echo "$name is already attached; keeping it"
    else
        gh release upload "$GITHUB_REF_NAME" "$file" -R "$GITHUB_REPOSITORY"
    fi
done
