include ../../Makefile.include

PARSER = bisonc++
FLAGS = -H "../LangNodes.h" --namespace lang

parse.cc: parser.y
	$(PARSER) $(FLAGS) $^
	sed -i "1i#pragma clang system_header" parser.h

parse.o: parse.cc ../lexer/lex.cc
	$(CC) $(CFLAGS) -c parse.cc

clean:
	$(RM) parserbase.h parser.h parser.h.gch parse.cc *.o
