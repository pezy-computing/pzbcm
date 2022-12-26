[![svlint](https://github.com/pezy-computing/pzbcm/actions/workflows/svlint.yml/badge.svg)](https://github.com/pezy-computing/pzbcm/actions/workflows/svlint.yml)

# PZBCM

This is a collection of basic common modules used in [PEZY Computing K.K.](https://www.pezy.co.jp/).

## List of Modules

* Basic Common Modules
    * [pzbcm_arbiter](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_arbiter)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_arbiter
    * [pzbcm_async_fifo](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_async_fifo)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_async_fifo
    * [pzbcm_async_handshake](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_async_handshake)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_async_handshake
    * [pzbcm_counter](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_counter)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_counter
    * [pzbcm_delay](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_delay)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_delay
    * [pzbcm_edge_detector](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_edge_detector)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_edge_detector
    * [pzbcm_fifo](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_fifo)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_fifo
    * [pzbcm_gray](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_gray)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_gray
    * [pzbcm_min_max_finder](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_min_max_finder)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_min_max_finder
    * [pzbcm_onehot](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_onehot)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_onehot
    * [pzbcm_selector](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_selector)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_selector
    * [pzbcm_slicer](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_slicer)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_slicer
    * [pzbcm_synchronizer](https://github.com/pezy-computing/pzbcm/tree/master/pzbcm_synchronizer)
        * wiki: https://github.com/pezy-computing/pzbcm/wiki/pzbcm_synchronizer

## Filelist

Filelist of PZBCM is written by using [flgen](https://github.com/pezy-computing/flgen).
Therefore, you need to geneate the filelist before using PZBCM. Example command is below.

```
$ flgen --output filelist.f path/to/pzbcm/pzbcm.list.rb
$ vcs -f filelist.f
```

## Supported EDA Tools

* Simulator
    * Synopsys VCS
    * Xilinx Vivado simulator
* Synthesis
    * Synopsys Design Compiler
    * Xilinx Vivado
* Other
    * Synopsys Formality

## License

PZBCM is released under the Apache-2.0 license. See [LICENSE](LICENSE) and below for further details.

    Copyright 2022 PEZY Computing K.K.

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

        http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
