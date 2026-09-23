#!/bin/bash
# Release: DELIERIUM_TAG=0.1.1 ./build.sh
set -euxo pipefail
uv version "$DELIERIUM_TAG"
uv lock
uv run pytest
git commit --all -m "Release $DELIERIUM_TAG"
git tag "$DELIERIUM_TAG"
rm -rf dist
uv build
git push
git push origin "$DELIERIUM_TAG"
uv publish
