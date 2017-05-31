%interactive
%filenames scanner

%%

[ \t\n]+
[0-9]+\.[0-9]+                      return lang::LangParser::DECIMAL;
[0-9]+                              return lang::LangParser::NUMBER;
while                               return lang::LangParser::WHILE;
if                                  return lang::LangParser::IF;
else                                return lang::LangParser::ELSE;
int                                 return lang::LangParser::INT;
float                               return lang::LangParser::FLOAT;
real                                return lang::LangParser::REAL;
bool                                return lang::LangParser::BOOL;
matrix\<                            return lang::LangParser::MATRIX;
light_matrix\<                      return lang::LangParser::LMATRIX;
==                                  return lang::LangParser::EQUALS;
!=                                  return lang::LangParser::NEQ;
&&                                  return lang::LangParser::AND;
\|\|                                return lang::LangParser::OR;
-\>                                 return lang::LangParser::IMPLIES;
\<o\>                               return lang::LangParser::ORIGINAL;
\<r\>                               return lang::LangParser::RELAXED;
-\.                                 return lang::LangParser::RMINUS;
\+\.                                return lang::LangParser::RPLUS;
\*\.                                return lang::LangParser::RTIMES;
\/\.                                return lang::LangParser::RDIV;
\<                                  return lang::LangParser::LT;
\<=                                 return lang::LangParser::LTEQ;
model\.                             return lang::LangParser::MODEL;
true                                return lang::LangParser::TRUE;
false                               return lang::LangParser::FALSE;
NORMAL                              return lang::LangParser::NORMAL;
skip                                return lang::LangParser::SKIP;
assert                              return lang::LangParser::ASSERT;
assume                              return lang::LangParser::ASSUME;
relational_assume                   return lang::LangParser::REL_ASSUME;
relational_assert                   return lang::LangParser::REL_ASSERT;
fail                                return lang::LangParser::FAIL;
COPY                                return lang::LangParser::COPY;
POW                                 return lang::LangParser::POW;
forall                              return lang::LangParser::FORALL;
fread                               return lang::LangParser::FREAD;
fwrite                              return lang::LangParser::FWRITE;
for                                 return lang::LangParser::FOR;
specvar                             return lang::LangParser::SPECVAR;
\+\+                                return lang::LangParser::OINCR;
--                                  return lang::LangParser::ODECR;
\+\+\.                              return lang::LangParser::INCR;
--\.                                return lang::LangParser::DECR;
[[:alpha:]_][[:alpha:][:digit:]_]*  return lang::LangParser::ID;
.                                   return matched()[0];

%%
