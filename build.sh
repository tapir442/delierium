#!/bin/bash -x
jupyterlab nbconvert README-GEN.ipynb --to html
git commit --all -m"Release $DELIERIUM_TAG"
pip wheel .
git tag $DELIERIUM_TAG
git push
git push origin $DELIERIUM_TAG
