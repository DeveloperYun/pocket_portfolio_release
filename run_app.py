from portfolio_tracker.bootstrap import bootstrap_runtime_patches
from portfolio_tracker.gui_app import run


def main() -> None:
    bootstrap_runtime_patches()
    run()


if __name__ == "__main__":
    main()

