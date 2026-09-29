import pytest


def pytest_addoption(parser):
    parser.addoption(
        "--run-too-slow",
        action="store_true",
        help="run the tests marked too_slow (symbolic Janet bases that do not finish)",
    )


def pytest_collection_modifyitems(config, items):
    if config.getoption("--run-too-slow"):
        return
    skip = pytest.mark.skip(reason="too slow: run with --run-too-slow")
    for item in items:
        if "too_slow" in item.keywords:
            item.add_marker(skip)
