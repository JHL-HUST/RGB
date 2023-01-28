# RGB
Relaxed Graph Color Bound for the Maximum $k$-plex Problem
----
This repository contains the code to the Maplex-RGB and KpLeX-RGB algorithms for the Maximum $k$-plex Problem (MkP) proposed in our paper: <br> <br>
[Relaxed Graph Color Bound for the Maximum k-plex Problem](https://arxiv.org/pdf/2301.07300) <br>
Jiongzhi Zheng, Mingming Jin, Yan Jin, Kun He <br> <br>

The source codes of Maplex and KpLeX can be downloaded from: <br>
https://github.com/ini111/Maplex <br>
https://github.com/huajiang-ynu/kplex <br> <br>

To run KpLeX-RGB, you need to execute the following commands on a Unix/Linux machine: <br> <br>

cd KpLeX-RGB <br>
./build <br>
./KpLeX-RGB *.col -x k <br> <br>

where *.col indicates the graph file. <br> <br>

To run Maplex-RGB, you need to execute the following commands on a Unix/Linux machine: <br> <br>

cd Maplex-RGB <br>
./build <br>
./maplex-RGB *.bin k cut-off <br> <br>

where *.bin indicates the binary graph file (see Maplex-RGB/README.txt for how to transform text graph file to binary graph file),  <br>
and cut-off indicates the cut-off time. <br> <br>

We provide some instances for testing, including DSJC125.1, Rand_100_0.05_5, san400-0-5-1, and socfb-Penn94. <br> <br>

We also provide all the generated 60 small random (binary) graphs for testing.  <br> <br>

More public instances can be downloaded from: <br>
http://cs.hbg.psu.edu/txn131/clique.html <br>
http://lcs.ios.ac.cn/~caisw/Resource/realworld%20graphs.tar.gz <br>
http://networkrepository.com/dimacs10.php <br> <br>

Contact
----
Questions and suggestions can be sent to jzzheng@hust.edu.cn. <br> <br>

Citation
----
If you find this code useful, please consider citing the original work by authors: <br>
```
@misc{zheng2022RGB,
  author={Jiongzhi Zheng and Mingming Jin and Yan Jin and Kun He},
  title={Relaxed Graph Color Bound for the Maximum $k$-plex Problem},
  journal={CoRR},
  volume={abs/2301.07300},
  year={2022},
  eprint="2301.07300",
  archivePrefix="arXiv"
}
```
