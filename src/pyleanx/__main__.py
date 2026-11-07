"""Allow ``python -m pyleanx ...`` (useful where the pyleanx.exe launcher is blocked)."""

import sys

from .cli import main

sys.exit(main())
