# hott-knaster-tarski-experiment-dissertation
Companion Coq script for the masters dissertation titled "Inductive and Coinductive Types in Homotopy Type Theory. An Experiment on the Knaster-Tarski Construction".

To run the script you need the HoTT library and a specially compiled version of Coq for the library. The script runs with the HoTT library of June 2016, but it will probably run with newer versions of the library.

Do the following:

1. Follow the installation instructions on file [INSTALL.md](https://github.com/HoTT/HoTT/blob/master/INSTALL.md) on the HoTT git repository:
   
   https://github.com/HoTT/HoTT

2. Once you have successfully compiled Coq and the HoTT library.  You can either use hoqide or Proof General. 

   To run hoqide, move to the root of the HoTT folder and execute: 
   
   ./hoqide
  
   Then, go to File -> Open and select the script file.

   However, I suggest you use Proof General, since previous versions of hoqide cause execution exceptions when running the script (the version of hoqide as of June
   2016 runs the script without problems). 

   If you encounter an exception in hoqide, you will have to use Proof General. Read file [INSTALL.md](https://github.com/HoTT/HoTT/blob/master/INSTALL.md)
   for details on setting up Proof General with your special version of Coq. 


