include ../Makefile.include

all: print

constrain: constrain.cpp parser/parse.o lexer/lex.o ModelNodes.o Z3Visitor.o OperatorVisitor.o
	$(CC) $(CFLAGS) $(WARN) $^ -o $@ -lz3

print: print.cpp parser/parse.o lexer/lex.o ModelNodes.o PrintVisitor.o
	$(CC) $(CFLAGS) $(WARN) $^ -o $@

lexer/lex.o: parser/parse.cc lexer/lex.cc
	$(MAKE) -C lexer lex.o

parser/parse.o: parser/parse.cc lexer/lex.cc
	$(MAKE) -C parser parse.o

ModelNodes.o: ModelNodes.cpp ModelNodes.h
	$(CC) $(CFLAGS) $(WARN) -c ModelNodes.cpp

PrintVisitor.o: PrintVisitor.h PrintVisitor.cpp
	$(CC) $(CFLAGS) $(WARN) -c PrintVisitor.cpp

Z3Visitor.o: Z3Visitor.h Z3Visitor.cpp
	$(CC) $(CFLAGS) $(WARN) -c Z3Visitor.cpp

OperatorVisitor.o: OperatorVisitor.h OperatorVisitor.cpp
	$(CC) $(CFLAGS) $(WARN) -c OperatorVisitor.cpp

parser/parse.cc: parser/parser.y
	$(MAKE) -C parser parse.cc

lexer/lex.cc: lexer/scanner.lex
	$(MAKE) -C lexer lex.cc

clean:
	$(MAKE) -C parser clean
	$(MAKE) -C lexer clean
	$(RM) constrain print *.o
