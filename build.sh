#!/bin/bash -x
jupyterlab nbconvert README-GEN.ipynb --to html
git add README-GEN.html
git commit --all -m"Release $DELIERIUM_TAG"
pip wheel .
git tag $DELIERIUM_TAG
git push
git push origin $DELIERIUM_TAG
twine upload delierium-$DELIERIUM_TAG-py*.whl
