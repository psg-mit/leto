include ../Makefile.include

all: print

chl: chl.cpp parser/parse.o lexer/lex.o LangNodes.o CHLVisitor.o
	$(CC) $(CFLAGS) $(WARN) $^ -o $@ -lz3

print: print.cpp parser/parse.o lexer/lex.o LangNodes.o PrintVisitor.o
	$(CC) $(CFLAGS) $(WARN) $^ -o $@

lexer/lex.o: parser/parse.cc lexer/lex.cc
	$(MAKE) -C lexer lex.o

parser/parse.o: parser/parse.cc lexer/lex.cc
	$(MAKE) -C parser parse.o

LangNodes.o: LangNodes.cpp LangNodes.h
	$(CC) $(CFLAGS) $(WARN) -c LangNodes.cpp

PrintVisitor.o: PrintVisitor.h PrintVisitor.cpp
	$(CC) $(CFLAGS) $(WARN) -c PrintVisitor.cpp

CHLVisitor.o: CHLVisitor.h CHLVisitor.cpp
	$(CC) $(CFLAGS) $(WARN) -c CHLVisitor.cpp

parser/parse.cc: parser/parser.y
	$(MAKE) -C parser parse.cc

lexer/lex.cc: lexer/scanner.lex
	$(MAKE) -C lexer lex.cc

clean:
	$(MAKE) -C parser clean
	$(MAKE) -C lexer clean
	$(RM) print chl *.o
