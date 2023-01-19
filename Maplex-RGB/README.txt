File format
The file of tobin transform text graph file to binary graph file.
Example for transform .txt file to .bin file.
g++ -g -o tobin/main tobin/main.cpp
./tobin/main random100_0.1.txt random100_0.1.bin


To compile the program
g++ -g -O3 -march=native -o maplex *.cpp

To run the program
./maplex random100_0.1.bin 2 1800
