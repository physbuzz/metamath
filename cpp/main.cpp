#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <cctype>
#include <vector>
#include <memory>


using namespace std;

#define MAX_CHAR 256

void help(){
    cout<<"Here is where I'd put a help file...\rIF I HAD ONE!!!"<<endl;
}

// After preprocessing, a database will consist of a sequence of statements. These are the scoping statements ${ and $}, along with the $c, $v, $f, $e, $d, $a, and $p statements.
enum class TokenType {
    CBEGIN,     // $(
    CEND,       // $)
    FBEGIN,     // $[ NOTE: file inclusion not supported
    FEND,       // $]
    BBEGIN,     // ${
    BEND,       // $}
    CONSTANT,   // $c
    VARIABLE,   // $v
    FLOATING,   // $f
    ESSENTIAL,  // $e
    DISJOINT,   // $d
    AXIOM,      // $a
    PROOF,      // $p
    END,        // $.
    EQUALS,     // $=
    STATEMENT,  // HI BADCOP
    SNULL
};

TokenType getTokenType(string arg){
    if(arg.length()==0){
        cerr<<"Arg length 0 in getTokenType?!"<<endl;
        return TokenType::SNULL;
    }
    if(arg[0]=='$'){
        if(arg.length()!=2){
            cerr<<"Statement "<<arg<<" must be length 2 in getTokenType?!"<<endl;
            return TokenType::SNULL;
        }
        switch(arg[1]){
            case  '(':
                return TokenType::CBEGIN;
            case  ')':
                return TokenType::CEND;
            case  '[':
                return TokenType::FBEGIN;
            case  ']':
                return TokenType::FEND;
            case  '{':
                return TokenType::BBEGIN;
            case  '}':
                return TokenType::BEND;
            case  'c':
                return TokenType::CONSTANT;
            case  'v':
                return TokenType::VARIABLE;
            case  'f':
                return TokenType::FLOATING;
            case  'e':
                return TokenType::ESSENTIAL;
            case  'd':
                return TokenType::DISJOINT;
            case  'a':
                return TokenType::AXIOM;
            case  'p':
                return TokenType::PROOF;
            case  '.':
                return TokenType::END;
            case  '=':
                return TokenType::EQUALS;
            default:
                cerr<<"Statement "<<arg<<" is not a valid Statement"<<endl;
                return TokenType::SNULL;
        }
    }
    return TokenType::STATEMENT;
}

string toString(TokenType type) {
    switch (type) {
        case TokenType::CBEGIN:    return "CBEGIN";
        case TokenType::CEND:      return "CEND";
        case TokenType::FBEGIN:    return "FBEGIN";
        case TokenType::FEND:      return "FEND";
        case TokenType::BBEGIN:    return "BBEGIN";
        case TokenType::BEND:      return "BEND";
        case TokenType::CONSTANT:  return "CONSTANT";
        case TokenType::VARIABLE:  return "VARIABLE";
        case TokenType::FLOATING:  return "FLOATING";
        case TokenType::ESSENTIAL: return "ESSENTIAL";
        case TokenType::DISJOINT:  return "DISJOINT";
        case TokenType::AXIOM:     return "AXIOM";
        case TokenType::PROOF:     return "PROOF";
        case TokenType::END:       return "END";
        case TokenType::EQUALS:    return "EQUALS";
        case TokenType::STATEMENT: return "STATEMENT";
        case TokenType::SNULL:     return "SNULL";
    }
    return "UNKNOWN";
}

// Note, these only metamath's labeled statement types.
enum class StatementType {
    FLOATING,
    ESSENTIAL,
    AXIOM,
    PROOF
};

enum class SymbolType {
    VARIABLE,
    CONSTANT
};

bool isValidChar(char arg){
    return arg>='!' && arg <= '~';
}

bool isWhitespace(char arg){
    return std::isspace(arg);
}

enum class TokenizerState{
    WHITESPACE,
    ACCUMULATING
};


/*

So what are we doing...

We maintain a global array of statements. 
Also global list of variables, constants.

bool identifierHasBeenUsed();

So what is a statement? A union type? Gross, no.
Statements are: $f, $e, $a, $p. Of these, $f$ carries very little data,
while $p$ potentially carries a lot. Something like
struct Statement{
    string label;

    //potentially bad overloading of SymbolType. It doesn't make sense for most things to be here.
    // Only allow f, e, a, p.
    SymbolType statementType; 

    SymbolID typecode;

    // List of symbols. For example, `t r s ( )`
    // For a floating hypothesis, symbols must have length 1 and statements must have length 0.
    vector<SymbolID> symbols;

    // Index into statement list.
    // "Every variable appearing in `statements` must have an active hypothesis
    vector<StatementID> statements;
}
*/
typedef int SymbolID;
typedef int StatementID;
struct Symbol
{
    string label;
    SymbolType symbolType;
};
struct Statement
{
    string label;
    StatementType statementType;
    SymbolID typecode;

    // For $f, require symbols.length()==1 and statements.length()==0.
    // For $e, require symbols.length()>=1 and statements.length()==0.
    // For $a, require symbols.length()>=1 and statements.length()>=1.
    // For $p, require symbols.length()>=1 and statements.length()>=1.
    // List of symbols. For example, `t r s ( )`
    vector<SymbolID> symbols;
    // Index into statement list.
    // "Every variable appearing in `statements` must have an active hypothesis
    vector<StatementID> statements;
};

enum class ParserState {
    NONE,    // not parsing a statement.
    VARIABLES, // Parsing a $v statement
    CONSTANTS, // Parsing a $c statement
    FLOATING_TYPE, // Parsing a $f statement, expecting typecode
    FLOATING_SYMBOLS, // Parsing a $f statement, expecting symbols
    ESSENTIAL_TYPE, // Parsing a $e statement, expecting typecode
    ESSENTIAL_SYMBOLS, // Parsing a $e statement, expecting symbols
    AXIOM_TYPE, // Parsing a $a statement, expecting typecode
    AXIOM_SYMBOLS, // Parsing a $a statement, expecting symbols
    PROOF_TYPE, // Parsing a $p statement, expecting typecode
    PROOF_SYMBOLS, // Parsing a $p statement, expecting symbols
    PROOF_PROOF, // Parsing a $p statement, expecting proof
};
class Metamath {
    bool commentSkip;
    bool errorState;
public:
    vector<Symbol> symbols;
    vector<Statement> statements;

    ParserState parserState;
    int blockDepth;
    string currentLabel;
    unique_ptr<Statement> currentStatement;

    Metamath() : commentSkip(false), errorState(false), parserState(ParserState::NONE), blockDepth(0) {
    }

    void parseBegin() {
    }

    SymbolID getSymbolID(string label) {
        for (size_t i = 0; i < symbols.size(); ++i) {
            if (symbols[i].label == label) {
                return static_cast<SymbolID>(i);
            }
        }
        return -1;
    }
    StatementID getStatementID(string label) {
        for (size_t i = 0; i < statements.size(); ++i) {
            if (statements[i].label == label) {
                return static_cast<StatementID>(i);
            }
        }
        return -1;
    }

    void parseWord(string word,int line){
        //cout<<toString(getTokenType(word))<<"  "<<word<<"  line  "<<line<<endl;
        if(errorState)
            return;
        auto stype=getTokenType(word);
        if(commentSkip) {
            if(stype==TokenType::CEND)
                commentSkip=false;
            return;
        }
        switch(stype) {
case TokenType::CBEGIN: 
            commentSkip=true;
            break;
case TokenType::CEND: 
            cerr<<"At line "<<line<<" comment end found outside of comment environment.";
            errorState=true;
            break;
case TokenType::FBEGIN: 
            cerr<<"At line "<<line<<" File inclusion not implemented.";
            errorState=true;
            break;
case TokenType::FEND:  
            cerr<<"At line "<<line<<" File inclusion not implemented.";
            errorState=true;
            break;
case TokenType::BBEGIN: 
            blockDepth++;
            break;
case TokenType::BEND:  
            if(blockDepth==0){
                cerr<<"At line "<<line<<" Block end found outside of block environment.";
                errorState=true;
            } else {
                blockDepth--;
            }
            break;
case TokenType::CONSTANT:  
            if(parserState!=ParserState::NONE){
                cerr<<"At line "<<line<<" Constant statement found while parsing another statement.";
                errorState=true;
            } else {
                parserState=ParserState::CONSTANTS;
            }
            break;
case TokenType::VARIABLE:  
            if(parserState!=ParserState::NONE){
                cerr<<"At line "<<line<<" Variable statement found while parsing another statement.";
                errorState=true;
            } else {
                parserState=ParserState::VARIABLES;
            }
            break;
case TokenType::FLOATING: 
            if(parserState!=ParserState::NONE){
                cerr<<"At line "<<line<<" Floating statement found while parsing another statement.";
                errorState=true;
                break;
            } 
            if(currentLabel.length()==0){
                cerr<<"At line "<<line<<" Floating statement found without a label.";
                errorState=true;
                break;
            } 
            currentStatement=make_unique<Statement>();
            currentStatement->label=currentLabel;
            currentStatement->statementType=StatementType::FLOATING;
            currentLabel="";
            parserState=ParserState::FLOATING_TYPE;
            break;
case TokenType::ESSENTIAL:
            if (parserState != ParserState::NONE) {
                cerr << "At line " << line << " Essential statement found while parsing another statement.";
                errorState = true;
                break;
            }
            if (currentLabel.length() == 0){
                cerr << "At line " << line << " Essential statement found without a label.";
                errorState = true;
                break;
            }
            currentStatement = make_unique<Statement>();
            currentStatement->label = currentLabel;
            currentLabel = "";
            parserState = ParserState::ESSENTIAL_TYPE;
            break;
case TokenType::DISJOINT:  
            cerr<<"At line "<<line<<" Disjoint statement found. Not implemented.";
            errorState=true;
            break;
case TokenType::AXIOM:     
            if (parserState != ParserState::NONE) {
                cerr << "At line " << line << " Axiom statement found while parsing another statement.";
                errorState = true;
                break;
            }
            if (currentLabel.length() == 0){
                cerr << "At line " << line << " Axiom statement found without a label.";
                errorState = true;
                break;
            }
            currentStatement = make_unique<Statement>();
            currentStatement->label = currentLabel;
            currentLabel = "";
            parserState = ParserState::AXIOM_TYPE;
            break;
case TokenType::PROOF:     
            if (parserState != ParserState::NONE) {
                cerr << "At line " << line << " Proof statement found while parsing another statement.";
                errorState = true;
                break;
            }
            if (currentLabel.length() == 0){
                cerr << "At line " << line << " Proof statement found without a label.";
                errorState = true;
                break;
            }
            currentStatement = make_unique<Statement>();
            currentStatement->label = currentLabel;
            currentLabel = "";
            parserState = ParserState::PROOF_TYPE;
            break;
case TokenType::END:       
            if(parserState==ParserState::NONE){
                cerr<<"At line "<<line<<" $. statement found while not parsing a statement.";
                errorState=true;
                break;
            }
            switch(parserState){
                case ParserState::VARIABLES:
                case ParserState::CONSTANTS:
                    break;
                case ParserState::FLOATING_SYMBOLS:
                case ParserState::ESSENTIAL_SYMBOLS:
                case ParserState::AXIOM_SYMBOLS:
                case ParserState::PROOF_PROOF:
                    statements.push_back(*currentStatement);
                    currentStatement.reset();
                    break;
                default:
                    cerr<<"At line "<<line<<" $. statement found while parsing a statement, but not at the end of a statement.";
                    errorState=true;
                    break;
            }
            parserState=ParserState::NONE;
            break;
case TokenType::EQUALS:    
            if(parserState!=ParserState::PROOF_SYMBOLS){
                cerr<<"At line "<<line<<" $= statement found while not parsing a proof statement.";
                cerr<<"This guy: "<<word<<".";
                errorState=true;
                break;
            }
            parserState=ParserState::PROOF_PROOF;
            break;
case TokenType::STATEMENT: 
            switch(parserState){
                case ParserState::NONE:
                    if(currentLabel.length()!=0){
                        cerr<<"At line "<<line<<" Label "<<word
                        <<" found while label "<<currentLabel<<" is still active.";
                        errorState=true;
                        break;
                    }
                    currentLabel=word;
                    break;
                case ParserState::VARIABLES:
                    // TODO: check label doesn't exist
                    symbols.push_back({word,SymbolType::VARIABLE});
                    break;
                case ParserState::CONSTANTS:
                    // TODO: check label doesn't exist
                    symbols.push_back({word,SymbolType::CONSTANT});
                    break;
                case ParserState::FLOATING_TYPE:
                    currentStatement->typecode=getSymbolID(word);
                    parserState=ParserState::FLOATING_SYMBOLS;
                    break;
                case ParserState::ESSENTIAL_TYPE:
                    currentStatement->typecode=getSymbolID(word);
                    parserState=ParserState::ESSENTIAL_SYMBOLS;
                    break;
                case ParserState::AXIOM_TYPE:
                    currentStatement->typecode=getSymbolID(word);
                    parserState=ParserState::AXIOM_SYMBOLS;
                    break;
                case ParserState::PROOF_TYPE:
                    currentStatement->typecode=getSymbolID(word);
                    parserState=ParserState::PROOF_SYMBOLS;
                    break;
                case ParserState::FLOATING_SYMBOLS:
                    currentStatement->symbols.push_back(getSymbolID(word));
                    break;
                case ParserState::ESSENTIAL_SYMBOLS:
                    currentStatement->symbols.push_back(getSymbolID(word));
                    break;
                case ParserState::AXIOM_SYMBOLS:
                    currentStatement->symbols.push_back(getSymbolID(word));
                    break;
                case ParserState::PROOF_SYMBOLS:
                    currentStatement->symbols.push_back(getSymbolID(word));
                    break;
                case ParserState::PROOF_PROOF:
                    currentStatement->statements.push_back(getStatementID(word));
                    break;
            }
            break;
case TokenType::SNULL:     
default:
            
            cerr<<"At line "<<line<<" File inclusion not implemented.";
            break;
        }
    }
    void parseEnd() {
    }
};

int main(int argc, char** argv){
    if(argc<2){
        help();
        return 1;
    }
    ifstream file(argv[1]);

    if(!file){
        cerr<<"Couldn't open file :'("<<endl;
        return 1;
    }

    char c;
    TokenizerState ts=TokenizerState::WHITESPACE;
    string identifier="";
    int line=1;
    Metamath mm;
    while(file.get(c)){
        if(isWhitespace(c)){
            if(c=='\r'||c=='\n'){
                line++;
            }
            if(ts==TokenizerState::ACCUMULATING){
                ts=TokenizerState::WHITESPACE;
                mm.parseWord(identifier,line);
            }
        } else if(isValidChar(c)) {
            if(ts==TokenizerState::WHITESPACE){
                identifier=std::string("")+c; 
                ts=TokenizerState::ACCUMULATING;
            } else if(ts==TokenizerState::ACCUMULATING){
                identifier+=c;
            }
        } else {
            cerr<<"Invalid character "<<c<<" encountered at line "<<line;
        }
    }
    if(ts==TokenizerState::ACCUMULATING){
        ts=TokenizerState::WHITESPACE;
        mm.parseWord(identifier,line);
    } 
    cout<<endl;
    return 0;
}












