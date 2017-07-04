%interactive
%filenames scanner

%%

[ \t\n]+
[0-9]+\.[0-9]+                      return model::ModelParser::DECIMAL;
[0-9]+                              return model::ModelParser::NUMBER;
true                                return model::ModelParser::TRUE;
false                               return model::ModelParser::FALSE;
bool                                return model::ModelParser::BOOL;
int                                 return model::ModelParser::INT;
real                                return model::ModelParser::REAL;
==                                  return model::ModelParser::EQUALS;
&&                                  return model::ModelParser::AND;
\|\|                                return model::ModelParser::OR;
operator                            return model::ModelParser::OPERATOR;
when                                return model::ModelParser::WHEN;
ensures                             return model::ModelParser::ENSURES;
modifies                            return model::ModelParser::MODIFIES;
fread                               return model::ModelParser::FREAD;
fwrite                              return model::ModelParser::FWRITE;
\<=                                 return model::ModelParser::LTEQ;
old                                 return model::ModelParser::OLD;
@region                             return model::ModelParser::REGION;
[[:alpha:]_][[:alpha:][:digit:]_]*  return model::ModelParser::ID;
.                                   return matched()[0];

%%
