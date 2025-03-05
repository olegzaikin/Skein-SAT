CPP = g++
CPPFLAGS = -O3 -std=c++20 -fopenmp

find_weak_outputs_skein: find_weak_outputs_skein.o
	${CPP} ${CPPFLAGS} find_weak_outputs_skein.o -o find_weak_outputs_skein

find_weak_outputs_skein.o: find_weak_outputs_skein.cpp
	${CPP} ${CPPFLAGS} find_weak_outputs_skein.cpp -c

clean:
	rm -rf *.o
	rm find_weak_outputs_skein
	clear
