from setuptools import setup, find_packages
setup(
    name="delierium",
    version="0.0.1.dev0",
    packages=find_packages(include=['delierium.*']),
    setup_requires=["more-itertools", "sage"],
    install_requires=["more-itertools", "sage"],
    author='Martin Mayerhofer-Schöpf',
    author_email='tapir@aon.at',
    license='MIT',
    classifiers=[],
    keywords='ODE PDE Lie',
    project_urls={'Source': 'https://github.com/tapir442/delierium'}
)
