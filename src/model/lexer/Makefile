include ../../Makefile.include

LEXER = flexc++
FLAGS = --namespace=model

lex.cc: scanner.lex
	$(LEXER) $(FLAGS) $^
	sed -i "1i#pragma clang system_header" scanner.h

lex.o: ../parser/parse.cc lex.cc
	$(CC) $(CFLAGS) -c lex.cc

clean:
	$(RM) lex.cc scannerbase.h scanner.h *.o
