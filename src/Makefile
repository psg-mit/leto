include Makefile.include

leto: main.cpp \
	    common.o \
	    lang/lexer/lex.o \
			lang/parser/parse.o \
			lang/CHLVisitor.o \
			lang/ConjunctionBreaker.o \
			lang/OldWrapper.o \
			lang/PrintVisitor.o \
			model/lexer/lex.o \
			model/parser/parse.o \
			model/Z3Visitor.o \
			lang/LangNodes.o \
			model/ModelNodes.o \
			model/OperatorVisitor.o
	$(CC) $(CFLAGS) $(WARN) $^ -o $@ -lz3

common.o: common.cpp common.h
	$(CC) $(CFLAGS) $(WARN) -c common.cpp

lang/lexer/lex.o: lang/lexer/scanner.lex
	$(MAKE) -C lang lexer/lex.o

lang/parser/parse.o: lang/parser/parser.y
	$(MAKE) -C lang parser/parse.o

model/lexer/lex.o: model/lexer/scanner.lex
	$(MAKE) -C model lexer/lex.o

model/parser/parse.o: model/parser/parser.y
	$(MAKE) -C model parser/parse.o

lang/CHLVisitor.o: lang/CHLVisitor.cpp lang/CHLVisitor.h
	$(MAKE) -C lang CHLVisitor.o

lang/ConjunctionBreaker.o: lang/ConjunctionBreaker.cpp lang/ConjunctionBreaker.h
	$(MAKE) -C lang ConjunctionBreaker.o

lang/OldWrapper.o: lang/OldWrapper.cpp lang/OldWrapper.h
	$(MAKE) -C lang OldWrapper.o

lang/PrintVisitor.o: lang/PrintVisitor.cpp lang/PrintVisitor.h
	$(MAKE) -C lang PrintVisitor.o

model/Z3Visitor.o: model/Z3Visitor.cpp model/Z3Visitor.h
	$(MAKE) -C model Z3Visitor.o

lang/LangNodes.o: lang/LangNodes.h lang/LangNodes.cpp
	$(MAKE) -C lang LangNodes.o

model/ModelNodes.o: model/ModelNodes.h model/ModelNodes.cpp
	$(MAKE) -C model ModelNodes.o

model/OperatorVisitor.o: model/OperatorVisitor.h model/OperatorVisitor.cpp
	$(MAKE) -C model OperatorVisitor.o

clean:
	$(MAKE) -C lang clean
	$(MAKE) -C model clean
	$(RM) leto *.o
