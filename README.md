
This repository is a fork of the [Nominal SSProve](https://github.com/MarkusKL/nominal-ssprove/tree/master) repository by Markus Krabbe Larsen.

The file `theories/Example/PRFMAC.v` is copied from the [SSProve](https://github.com/SSProve/ssprove/blob/main/theories/Crypt/examples/PRFMAC.v) repository, and is edited in accordance with our Research Project at the IT University of Copenhagen in the fall 2024. This is the only file we have worked on in this fork of the Nominal SSProve repository.

# How to run

1. Install nix-shell in your shell of choice: [Nix-shell installation guide](https://nixos.org/download/#nix-install-linux).
2. Download the repository.
3. Open the repository folder in your shell and initialize the nix-shell by running the command `nix-shell`. This might take a while the first time.
4. When the loading has finished, and you're in the nix-shell, run the `make` command to compile the Coq files.
5. Then run the command `coqide theories/Example/PRFMAC.v` to open the file in CoqIDE.
6. In CoqIDE you should now be able to step through the file and the final proof.

=======

# Nominal-SSProve

Install dependencies by entering the nix-shell with command `nix-shell` or using the docker environment as described below.

Check all project files using `make` and inspect files using vim (with Coqtail).

## Docker environment

Build image with Coq dependencies and enter shell with commands:

```
docker build -t nominal-ssprove .
docker run --rm -it -v ${PWD}:/mnt nominal-ssprove
```

It takes around an hour to build the image due to compilation of Coq dependencies, but progress should be evident by terminal output.
The final image is around 4GB in size and can be deleted with the command `docker rmi nominal-ssprove`.

