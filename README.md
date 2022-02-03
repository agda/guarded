# Guarded Cubical Agda library.

## Forcing ticks extension.

As of now support for forcing ticks (e.g. ◇) is to be found in the
`forcing-ticks` branch of Agda's main repo. It can be obtained and installed like so:

```
   $ git clone https://github.com/agda/agda.git
   $ cd agda
   $ git checkout forcing-ticks
   $ cabal install
```

See also: https://agda.readthedocs.io/en/latest/getting-started/installation.html#installation-from-source


The `forcing-ticks` branch of this repo contains the version of this
library making use of forcing ticks:

```
   $ git clone https://github.com/agda/guarded.git
   $ cd guarded
   $ git checkout forcing-ticks
```

For how to install Agda libraries see: https://agda.readthedocs.io/en/latest/tools/package-system.html
