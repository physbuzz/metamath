#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <cctype>


using namespace std;

#define MAX_CHAR 256

void help(){
    cout<<"Here is where I'd put a help file...\rIF I HAD ONE!!!"<<endl;
}

// After preprocessing, a database will consist of a sequence of statements. These are the scoping statements ${ and $}, along with the $c, $v, $f, $e, $d, $a, and $p statements.
enum class SType {
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

SType getStatementType(string arg){
    if(arg.length()==0){
        cerr<<"Arg length 0 in getStatementType?!"<<endl;
        return SType::SNULL;
    }
    if(arg[0]=='$'){
        if(arg.length()!=2){
            cerr<<"Statement "<<arg<<" must be length 2 in getStatementType?!"<<endl;
            return SType::SNULL;
        }
        switch(arg[1]){
            case  '(':
                return SType::CBEGIN;
            case  ')':
                return SType::CEND;
            case  '[':
                return SType::FBEGIN;
            case  ']':
                return SType::FEND;
            case  '{':
                return SType::BBEGIN;
            case  '}':
                return SType::BEND;
            case  'c':
                return SType::CONSTANT;
            case  'v':
                return SType::VARIABLE;
            case  'f':
                return SType::FLOATING;
            case  'e':
                return SType::ESSENTIAL;
            case  'd':
                return SType::DISJOINT;
            case  'a':
                return SType::AXIOM;
            case  'p':
                return SType::PROOF;
            case  '.':
                return SType::END;
            case  '=':
                return SType::EQUALS;
            default:
                cerr<<"Statement "<<arg<<" is not a valid Statement"<<endl;
                return SType::SNULL;
        }
    }
    return SType::STATEMENT;
}

string toString(SType type) {
    switch (type) {
        case SType::CBEGIN:    return "CBEGIN";
        case SType::CEND:      return "CEND";
        case SType::FBEGIN:    return "FBEGIN";
        case SType::FEND:      return "FEND";
        case SType::BBEGIN:    return "BBEGIN";
        case SType::BEND:      return "BEND";
        case SType::CONSTANT:  return "CONSTANT";
        case SType::VARIABLE:  return "VARIABLE";
        case SType::FLOATING:  return "FLOATING";
        case SType::ESSENTIAL: return "ESSENTIAL";
        case SType::DISJOINT:  return "DISJOINT";
        case SType::AXIOM:     return "AXIOM";
        case SType::PROOF:     return "PROOF";
        case SType::END:       return "END";
        case SType::EQUALS:    return "EQUALS";
        case SType::STATEMENT: return "STATEMENT";
        case SType::SNULL:     return "SNULL";
    }
    return "UNKNOWN";
}


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

    //potentially bad overloading of SType. It doesn't make sense for most things to be here.
    // Only allow f, e, a, p.
    SType statementType; 

    SymbolID typecode;

    // List of symbols. For example, `t r s ( )`
    // For a floating hypothesis, symbols must have length 1 and statements must have length 0.
    vector<SymbolID> symbols;

    // Index into statement list.
    // "Every variable appearing in `statements` must have an active hypothesis
    vector<StatementID> statements;
}
*/
class Metamath {
    bool commentSkip;
    bool errorState;
public:
    typedef int SymbolID;
    typedef int StatementID;
    struct Symbol {
        
    }
    struct Statement{
        string label;
        // Though we have an SType here, the only valid things are:
        // f (SType::FLOATING)
        // e (SType::ESSENTIAL)
        // a (SType::AXIOM)
        // p (SType::PROOF)
        SType statementType; 
        SymbolID typecode;
        // List of symbols. For example, `t r s ( )`
        // For a floating hypothesis, symbols must have length 1 and statements must have length 0.
        vector<SymbolID> symbols;
        // Index into statement list.
        // "Every variable appearing in `statements` must have an active hypothesis
        vector<StatementID> statements;
    }

    Metamath() : commentSkip(false), errorState(false) { }

    void parseBegin() {
    }

    void parseWord(string word,int line){
        //cout<<toString(getStatementType(word))<<"  "<<word<<"  line  "<<line<<endl;
        if(errorState)
            return;
        auto stype=getStatementType(word);
        if(commentSkip) {
            if(stype==SType::CEND)
                commentSkip=false;
            return;
        }
        switch(stype) {
case SType::CBEGIN: 
            commentSkip=true;
            break;
case SType::CEND: 
            cerr<<"At line "<<line<<" comment end found outside of comment environment.";
            errorState=true;
            break;
case SType::FBEGIN: 
            cerr<<"At line "<<line<<" File inclusion not implemented.";
            errorState=true;
            break;
case SType::FEND:  
            cerr<<"At line "<<line<<" File inclusion not implemented.";
            errorState=true;
            break;
case SType::BBEGIN: 
case SType::BEND:  
case SType::CONSTANT:  
case SType::VARIABLE:  
case SType::FLOATING: 
case SType::ESSENTIAL: 
case SType::DISJOINT:  
case SType::AXIOM:     
case SType::PROOF:     
case SType::END:       
case SType::EQUALS:    
case SType::STATEMENT: 
            std::cout<<word<<" ";
            break;
case SType::SNULL:     
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












