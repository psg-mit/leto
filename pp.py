#!/usr/bin/env python3

import subprocess
import sys

CMD = "cpp -E "

if __name__ == "__main__":
    assert len(sys.argv) == 3

    model_cmd = CMD + sys.argv[1]
    prog_cmd = CMD + sys.argv[2]

    # Send model to cpp and process the result
    model_out = subprocess.check_output(model_cmd,
                                        shell=True,
                                        universal_newlines=True)
    for line in model_out.split("\n"):
        if line and not line.startswith("#"):
            print(line)

    # Newline indicates start of program
    print("")

    # Send processed program
    prog_out = subprocess.check_output(prog_cmd,
                                       shell=True,
                                       universal_newlines=True)
    for line in prog_out.split("\n"):
        if line and not line.startswith("#"):
            print(line)
