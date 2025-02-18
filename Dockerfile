FROM nixos/nix
COPY shell.nix pkgs.nix pin.nix pin.json /mnt/
WORKDIR /mnt
RUN nix-shell --run "echo ok"
ENTRYPOINT nix-shell
