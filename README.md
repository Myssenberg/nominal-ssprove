This repository is a fork of the [Nominal SSProve](https://github.com/MarkusKL/nominal-ssprove/tree/master) repository by Markus Krabbe Larsen.

The folder `theories/Cryptobox/` has been added for our Master's Thesis at the IT University of Copenhagen in the spring of 2025.
The `theories/Cryptobox/` folder contains 17 files, and these are the only files we have worked on in this fork of the Nominal SSProve repository.

# How to run

1. Install nix-shell in your shell of choice: [Nix-shell installation guide](https://nixos.org/download/#nix-install-linux).
2. Download the repository.
3. Open the repository folder in your shell and initialize the nix-shell by running the command `nix develop` (or `nix develop --extra-experimental-features nix-command --extra-experimental-features flakes`). This might take a while the first time.
4. When the loading has finished, and you are in the nix-shell, run the `make` command to compile the Coq files.
5. Then run the command `coqide theories/Cryptobox/[FILENAME].v` to open one of the files in CoqIDE.
6. In CoqIDE you should now be able to step through the content of the files, including the proofs.

---

The README from the original repository:

# Nominal-SSProve

Install dependencies by entering the nix development environment with command `nix develop` or using the docker environment as described below.
It is recommended to use the `coq`, `coq-community` and `math-comp` nix caches to significantly initial build time.

Check all project files using `make` and inspect files using vim (with Coqtail) or CoqIDE.

## Docker environment

Build image with Coq dependencies and enter shell with commands:

```
docker build -t nominal-ssprove .
docker run --rm -it nominal-ssprove
```

The project files are copied into the image, so changes made will not propagate to the host filesystem.
The final image is around 4GB in size and can be deleted with the command `docker rmi nominal-ssprove`.
