============
Installation
============

Latest release
--------------

`hs-to-rocq` is not published on Hackage. Install from source (see below).

Development version
-------------------

The source code for the development version is available via github. This
repository includes everything that you need.
 
.. code-block:: shell

    $ git clone https://github.com/plclub/hs-to-coq.git hs-to-rocq
    $ cd hs-to-rocq

The recommended way of building `hs-to-rocq` is to use the `stack` tool which you can get from https://docs.haskellstack.org/en/stable/README/. If you
have not setup stack before

.. code-block:: shell

   $ stack setup

To build ``hs-to-rocq``

.. code-block:: shell

   $ stack build

Coq Requirements
----------------

This repository comes with a Coq version of the Haskell `base
<https://github.com/plclub/hs-to-coq/tree/master/base>`_ library, used by the
output of ``hs-to-rocq``.

You must have `Coq 8.20` and `MathComp` (with Hierarchy Builder) to build
the base library and containers proofs. You can install these tools using
`opam <https://opam.ocaml.org/>`_.

.. code-block::  shell

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update
    $ opam install coq.8.20.1 coq-mathcomp-ssreflect coq-hierarchy-builder


Once installed, you can build the base library from the project root with

.. code-block:: shell

    $ cd base && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..

The directory `base-thy
<https://github.com/plclub/hs-to-coq/tree/master/base-thy>`_ contains auxiliary
definitions and lemmas, such as lawful type-class instances. You can build
these with

.. code-block:: shell

    $ cd base-thy && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..

Test your hs-to-rocq installation
--------------------------------

To test whether your `hs-to-rocq` installation is successful, you can try to
compile the examples that are distributed with the tool.

Some examples use git submodules. If you only want to **build the
pre-generated Coq files** (proofs, libraries), a shallow init is enough:

.. code-block:: shell

    $ git submodule update --init

If you want to **regenerate Coq modules from Haskell source** (e.g. to test
edits or work on hs-to-rocq itself), you also need the GHC and containers
source trees:

.. code-block:: shell

    $ git submodule update --init examples/ghc/ghc
    $ git submodule update --init examples/containers/containers

Note that these submodules are large and may take a while to download.

Then, compile all of the examples with

.. code-block:: shell

    $ cd examples
    $ ./boot.sh

The flag `noclean` will recompile everything without first deleting the old
versions.

.. code-block:: shell

    $ ./boot.sh noclean

The flag `quick` is like the above but doesn't run the tests.

.. code-block:: shell

    $ ./boot.sh quick


Troubleshooting
--------------------------------

1. lndir: command not found

On Mac OSX, you may need to install XQuartz and imake to run `examples/boot.sh`. 

If you get the error message while trying to run `./boot.sh`: 

.. code-block:: shell

    > lndir: command not found
   
The following commands will install XQuartz and imake through `brew`:

.. code-block:: shell

    $ brew install --cask xquartz
    $ brew install imake
    
Depending on your `brew cask` setup, you may also need to update your $PATH
variable. 

.. code-block:: shell

    $ export PATH=$PATH:/usr/X11/bin >> ~/.bash_profile
    
2. git submodule update --init gives error fatal: Needed a single revision

Try removing the submodule directory that the error was triggered on, and run the command again.
(i.e. If the error was on `examples/wc/wc`, a `rm -rf examples/wc/wc` followed by a
`git submodule update --init` will do the trick.)
