from setuptools import setup, find_packages
from setuptools.command.build_py import build_py as build_py_orig
import pathlib
import fnmatch

here = pathlib.Path(__file__).parent.resolve()

excluded = []
class build_py(build_py_orig):
    def find_package_modules(self, package, package_dir):
        modules = super().find_package_modules(package, package_dir)
        return [
            (pkg, mod, file)
            for (pkg, mod, file) in modules
            if not any(fnmatch.fnmatchcase(file, pat=pattern) for pattern in excluded)
        ]

# Get the long description from the README file
long_description = (here / 'README.md').read_text(encoding='utf-8')

setup(
    name="delierium",
    version="0.9.0.dev12",
    description="Symmetry Analysis for ODEs/PDEs using SageMath",
    long_description=long_description,
    long_description_content_type='text/markdown',
    setup_requires=["more-itertools", "anytree"],
    install_requires=["more-itertools", "anytree"],
    python_requires = ">=3.11",
    author='Martin Mayerhofer-Schöpf',
    author_email='tapir@aon.at',
    license='MIT',
    classifiers=[
        'Development Status :: 3 - Alpha',
        'Programming Language :: Python :: 3 :: Only',
        'License :: OSI Approved :: MIT License',
        'Intended Audience :: Science/Research',
        'Topic :: Scientific/Engineering :: Mathematics'
        ],
    keywords='ODE PDE Lie Symmetry',
    cmdclass={'build_py': build_py},
    package_data={'delierium/notebooks' : ['notebooks/Arrigo_Chapter_2.5.ipynb']},
    project_urls={'Source': 'https://github.com/tapir442/delierium'}
)
