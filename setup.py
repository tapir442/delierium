from setuptools import setup, find_packages
import pathlib

here = pathlib.Path(__file__).parent.resolve()

# Get the long description from the README file
long_description = (here / 'README.md').read_text(encoding='utf-8')

setup(
    name="delierium",
    version="0.9.0.dev0",
    description="Symmetry Analysis for ODEs/PDEs using SageMath",
    long_description=long_description,
    long_description_content_type='text/markdown',
    setup_requires=["more-itertools"],
    install_requires=["more-itertools"],
    python_requires = ">=3.10",
    author='Martin Mayerhofer-Schöpf',
    author_email='tapir@aon.at',
    license='MIT',
    classifiers=[
        'Development Status :: 3 - Alpha',
        'Programming Language :: Python :: 3 :: Only',
        'License :: OSI Approved :: MIT License',
        'Intended Audience :: Mathematicians',
        'Intended Audience :: Science/Research',
        'Topic :: Calculus :: ODE',
        'Topic :: Scientific/Engineering :: Mathematics'
        ],
    keywords='ODE PDE Lie Symmetry',
    packages=find_packages(include=['delierium']),    
    package_data={'delierium' : ['*/Arrigo_Chapter_2.5.ipynb']},
    project_urls={'Source': 'https://github.com/tapir442/delierium'}
)
