all: pa

parser.ypp: gen-datatype.sh parser.ypp.in
	./gen-datatype.sh < parser.ypp.in > parser.ypp
lex.yy.cpp: scanner.lpp
	flex -o lex.yy.cpp scanner.lpp
parser.tab.cpp parser.tab.hpp stack.hh: parser.ypp
	/opt/bison-3.0.3/bin/bison -do parser.tab.cpp parser.ypp
pa: lex.yy.cpp parser.tab.cpp parser.tab.hpp stack.hh
	$(CXX) -std=c++14 -g -Wall -Wno-unused-function -o pa lex.yy.cpp parser.tab.cpp -lsh
