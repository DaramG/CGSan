# CGSan
CGSan is a static analysis tool that finds a kind of use-after-free bug in a program based on compacting garbage collection, which we refer to as use-after-compacting-gc.
The definition of use-after-compacting-gc and the details of how CGSan works is in our [paper](https://www.usenix.org/system/files/sec21-han-hyungseok.pdf), "Precise and Scalable Detection of Use-after-Compacting-Garbage-Collection Bugs" (Usenix Security 2021).

# Installation
1. Install dotnet

Installation of `dotnet` depends on OS, so please check this [link](https://dotnet.microsoft.com/download/linux-package-manager/ubuntu18-04/sdk-current).

2. Clone and build `FsSymExe`
```
$ git clone git@github.com:DaramG/CGSan.git
$ cd CGSan
$ git submodule init
$ git submodule update
$ cd lib/FsSymExe; make
```

3. Build `CGSan`
```
$ cd CGSan
$ dotnet build -c Release
```

# Usage

```
dotnet bin/Main.dll analyze `<target name> (v8 | moz)` `<LLVM IR file path>`
```


# Citation
If you plan to use CGSan, please consider citing our [paper](https://www.usenix.org/system/files/sec21-han-hyungseok.pdf):
```
@INPROCEEDINGS{han:usenixsec:2021,
  author = {HyungSeok Han and Andrew Wesie and Brian Pak},
  title = {Precise and Scalable Detection of {Use-after-Compacting-Garbage-Collection Bugs}},
  booktitle = usenixsec,
  year = 2021
}
```
