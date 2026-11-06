#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <cctype>
#include <vector>
#include <memory>
#include <algorithm>
#include <set>


#define VERBOSE

using namespace std;

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
    TOKEN,  // HI BADCOP
    SNULL
};

// Token types correspond to
// `$( $) $[ $] ${ $} $c $v $f $e $d $a $p $. $=`

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
    return TokenType::TOKEN;
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
        case TokenType::TOKEN: return "TOKEN";
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
    // For $a, require symbols.length()>=1 and statements.length()==0.
    // For $p, require symbols.length()>=1 and statements.length()>=1.
    // List of symbols. For example, `t r s ( )`
    vector<SymbolID> symbols;
    // Index into statement list.
    // "Every variable appearing in `statements` must have an active hypothesis
    vector<StatementID> statements;
    vector<StatementID> mandatory;
};



enum class CurrentParserState {
    NONE,    // not parsing a statement.
    VARIABLES, // Parsing a $v statement
    CONSTANTS, // Parsing a $c statement
    STATEMENT
};


string toString(CurrentParserState state) {
    switch (state) {
        case CurrentParserState::NONE: return "NONE";
        case CurrentParserState::VARIABLES: return "VARIABLES";
        case CurrentParserState::CONSTANTS: return "CONSTANTS";
        case CurrentParserState::STATEMENT: return "STATEMENT";
    }
    return "UNKNOWN";
}

enum class ParserStatementState {
    TYPECODE, SYMBOLS, PROOF
};

struct ParserState {
    bool errorState;
    bool commentSkip;
    string currentLabel;
    Statement currentStatement;

    vector<SymbolID> symbolStack;
    vector<int> symbolStackLevels;
    vector<StatementID> statementStack;
    vector<int> statementStackLevels;
    CurrentParserState parserState;
    StatementType currentStatementType;
    ParserStatementState currentStatementState;
};

struct ProofDatabase {
    vector<Symbol> symbols;
    vector<Statement> statements;
    Statement &getStatement(StatementID arg){
        return statements.at(arg);
    }
    const Statement &getStatement(StatementID arg) const{
        return statements.at(arg);
    }

    Symbol &getSymbol(SymbolID arg) {
        return symbols.at(arg);
    }
    const Symbol &getSymbol(SymbolID arg) const{
        return symbols.at(arg);
    }
    bool isVariable(SymbolID arg) const{
        return getSymbol(arg).symbolType==SymbolType::VARIABLE;
    }


    void printDatabase() {
        cout<<" =============== "<<endl;
        cout<<" === Symbols === "<<endl;
        cout<<" =============== "<<endl;
        for(size_t i=0;i<symbols.size();i++){
            cout<<i<<": "<<symbols[i].label;
            if(symbols[i].symbolType==SymbolType::CONSTANT)
                cout<<" (constant)"<<endl;
            else
                cout<<" (variable)"<<endl;
        }
        cout<<endl;
        cout<<" ================== "<<endl;
        cout<<" === Statements === "<<endl;
        cout<<" ================== "<<endl;
        for(size_t i=0;i<statements.size();i++){
            switch(statements[i].statementType){
            case StatementType::FLOATING:
                cout<<i<<": "<<statements[i].label
                    <<" $f "<< statements[i].typecode<<" "<< statements[i].symbols.at(0)<<" $. (floating hypothesis)"<<endl;
                break;
            case StatementType::ESSENTIAL:
                cout<<i<<": "<<statements[i].label
                    <<" $e "<< statements[i].typecode<<" ";
                for(size_t j=0;j<statements[i].symbols.size();j++){
                    cout<<statements[i].symbols.at(j)<<" ";
                }
                cout<<"$. (essential hypothesis)"<<endl;
                break;
            case StatementType::AXIOM:
                cout<<i<<": "<<statements[i].label
                    <<" $a "<< statements[i].typecode<<" ";
                for(size_t j=0;j<statements[i].symbols.size();j++){
                    cout<<statements[i].symbols.at(j)<<" ";
                }
                cout<<"$. (axiom)"<<endl;
                break;
            case StatementType::PROOF:
                cout<<i<<": "<<statements[i].label
                    <<" $p "<< statements[i].typecode<<" ";
                for(size_t j=0;j<statements[i].symbols.size();j++){
                    cout<<statements[i].symbols.at(j)<<" ";
                }
                cout<<endl;
                cout<<"$= ";
                for(size_t j=0;j<statements[i].statements.size();j++){
                    cout<<statements[i].statements.at(j)<<" ";
                }
                cout<< "$."<<endl;
                break;
            default:
                break;
            }
        }
    }
    // Get symbol ID, don't check if the symbol is active, just look in pdb.
    SymbolID getSymbolID(string label) {
        for (size_t i = 0; i < symbols.size(); ++i) {
            if (symbols[i].label == label) {
                return static_cast<SymbolID>(i);
            }
        }
        return -1;
    }

    // Get statement ID, don't check if the statement is active, just look in pdb.
    StatementID getStatementID(string label) {
        for (size_t i = 0; i < statements.size(); ++i) {
            if (statements[i].label == label) {
                return static_cast<StatementID>(i);
            }
        }
        return -1;
    }
};

class Metamath {
public:
    ProofDatabase pdb;
    ParserState ps;

    Metamath() : pdb(), ps() {
        ps.parserState = CurrentParserState::NONE;
        ps.statementStackLevels.push_back(0);
        ps.symbolStackLevels.push_back(0);
        ps.commentSkip=false;
        ps.errorState = false;
    }

    void parseBegin() {
    }

    bool symbolIDIsActive(SymbolID arg) {
        for(int i=0; i<ps.symbolStack.size(); i++) {
            if(arg==ps.symbolStack[i])
                return true;
        }
        return false;
    }
    bool statementIDIsActive(StatementID arg) {
        for(int i=0; i<ps.statementStack.size(); i++) {
            if(arg==ps.statementStack[i])
                return true;
        }
        return false;
    }
        
    // Get the statement that introduces the symbol with the given ID. 
    StatementID getActiveFloatingForSymbol(SymbolID id) {
        // This gets the statement, but not the active statement
        for(int i=0;i<ps.statementStack.size();i++){
            StatementID sid=ps.statementStack[i];
            const Statement &s=pdb.statements[sid];
            if(s.statementType==StatementType::FLOATING &&
                s.symbols.at(0)==id){
                return sid;
            }
        }
        return -1;
    }


    bool isSymbolActive(SymbolID id) {
        for (size_t i = 0; i < ps.symbolStack.size(); ++i) {
            if (ps.symbolStack[i] == id) {
                return true;
            }
        }
        return false;
    }
    bool isStatementActive(StatementID id) {
        if(pdb.statements.at(id).statementType==StatementType::AXIOM ||
              pdb.statements.at(id).statementType==StatementType::PROOF)
                return true;
        for (size_t i = 0; i < ps.statementStack.size(); ++i) {
            if (ps.statementStack[i] == id) {
                return true;
            }
        }
        return false;
    }

    void parserError(string message) {
        cerr << "Error while parsing: "<<message<<endl;
        ps.errorState = true;
    }
    void parserError(string message, int line, string token="") {
        if(token.length()>0)
            cerr << "Error at line " << line << " while parsing token \"" << token << "\": "
                 << message << " Token: " << token << endl;
        else
            cerr << "Error at line " << line << " while parsing: "
                 << message << endl;
        ps.errorState = true;
    }
    void getStatementsMandatorySet(std::set<StatementID> &mandatorySet, 
                const Statement &statement,
                int line, string token) {
        for (int i = 0; i < statement.symbols.size(); i++) {
            SymbolID id = statement.symbols[i];
            // check if it's a constant
            if (pdb.symbols[id].symbolType == SymbolType::CONSTANT)
                continue;
            // Look up the statement id:
            StatementID stat = getActiveFloatingForSymbol(id);
            if (stat < 0) {
                cerr << "Error while parsing: SymbolID=" << id
                     << ", symbol " << pdb.symbols[id].label
                     << " has no active floating hypothesis." << endl;
                cerr << "while parsing line " << line << ", token " << token << endl;
                ps.errorState = true;
                return;
            }
            mandatorySet.insert(stat);
        }
    }

    void pushStatement(int line, string token) {
        // Check the constraints I mentioned
        // For $f, require symbols.length()==1 and statements.length()==0.
        // For $e, require symbols.length()>=1 and statements.length()==0.
        // For $a, require symbols.length()>=1 and statements.length()==0.
        // For $p, require symbols.length()>=1 and statements.length()>=1.
        switch(ps.currentStatementType){
            case StatementType::FLOATING:
                if(ps.currentStatement.symbols.size()!=1){
                    parserError("Floating hypothesis must have exactly one symbol.", line, token);
                    return;
                }
                if(ps.currentStatement.statements.size()!=0){
                    parserError("Floating hypothesis cannot have statements.", line, token );
                    return;
                }
                break;
            case StatementType::ESSENTIAL:
                if(ps.currentStatement.symbols.size()<1){
                    parserError("Essential hypothesis must have at least one symbol.", line, token);
                    return;
                }
                if(ps.currentStatement.statements.size()!=0){
                    parserError("Essential hypothesis cannot have statements.", line, token);
                    return;
                }
                break;
            case StatementType::AXIOM:
                if(ps.currentStatement.symbols.size()<1){
                    parserError("Axiom must have at least one symbol.", line, token);
                    return;
                }
                if(ps.currentStatement.statements.size()!=0){
                    parserError("Axiom must have zero statements.", line, token);
                    return;
                }
                break;
            case StatementType::PROOF:
                if(ps.currentStatement.symbols.size()<1){
                    parserError("Proof must have at least one symbol.", line, token);
                    return;
                }
                if(ps.currentStatement.statements.size()<1){
                    parserError("Proof must have at least one statement.", line, token);
                    return;
                }
                break;
            default:
                parserError("Unknown statement type.");
                return;
        }
        /* To find the mandatory hypotheses, it's a lil convoluted, 
        we'll do it in a slow O(N^2) way. Step 1 is to go up the list of active 
        hypotheses and collect all essential hypotheses in a set, while parsing 
        them. For any variable in an essential hypothesis, or variable in the 
        symbols list of the statement itself, we find the floating hypothesis t
        hat defines that variable, and add it to the list of mandatory 
        hypotheses. Finally, we do a second pass up the list of active 
        hypotheses (iterate from 0), and push anything in our set to the 
        list of mandatory hypotheses.

        Mandatory hypotheses only need to be computed for assertions, that is,
        for $a and $p statements. For $f and $e statements, `statment.mandatory` should
        be empty. 
        */
        if(ps.currentStatement.statementType!=StatementType::FLOATING 
           && ps.currentStatement.statementType!=StatementType::ESSENTIAL){
            std::set<StatementID> mandatorySet;
            getStatementsMandatorySet(mandatorySet, ps.currentStatement,
                 line, token);
            for(int i=0;i<ps.statementStack.size();i++) {
                StatementID id=ps.statementStack[i];
                Statement &s=pdb.statements.at(id);
                if(s.statementType!=StatementType::ESSENTIAL)
                    continue;
                mandatorySet.insert(id);
                getStatementsMandatorySet(mandatorySet, s, line, token);
            }
            for(int i=0;i<ps.statementStack.size();i++) {
                StatementID id=ps.statementStack[i];
                if(mandatorySet.count(id)>0)
                    ps.currentStatement.mandatory.push_back(id);
            }
        }
        
        //Finally, push.
        if(ps.errorState) {
            cerr<<"GOTCHA!!!!!!"<<endl;
            return;
        }
        if(ps.currentStatement.statementType == StatementType::FLOATING) {
            // Extra check to make sure we don't redeclare a symbol
            StatementID sid = getActiveFloatingForSymbol(ps.currentStatement.symbols.at(0));
            if(sid!=-1){
                parserError("Floating hypothesis for symbol " + 
                    pdb.symbols[ps.currentStatement.symbols.at(0)].label +
                    " already defined in statement " + 
                    pdb.statements[sid].label, line, token);
                return;
            }
        }
        pdb.statements.push_back(ps.currentStatement);
        ps.currentStatement = Statement();
        ps.statementStack.push_back(pdb.statements.size() - 1);
        ps.statementStackLevels.back() += 1;
    }

    void parseSwitchToStatement(StatementType stype, int line, string word) {
        if(ps.parserState!=CurrentParserState::NONE){
            parserError("Cannot be in state " + 
                toString(ps.parserState)
                + " while starting a statement.", line, word);
            return;
        }
        if(ps.currentLabel==""){
            parserError("Statement cannot have empty label.", line, word);
            return;
        }
        if(pdb.getSymbolID(ps.currentLabel)!=-1){
            parserError("Statement " + ps.currentLabel + " already defined as a symbol.", line, word);
            return;
        }
        StatementID statementIDLookup=pdb.getStatementID(ps.currentLabel);
        if(statementIDLookup!=-1){
            if(stype==StatementType::FLOATING){
                parserError("Statement " + ps.currentLabel + " already defined.", line, word);
                return;
            }
        }
        ps.parserState=CurrentParserState::STATEMENT;
        ps.currentStatement.label=ps.currentLabel;
        ps.currentStatement.statementType=stype;
        ps.currentLabel="";
        ps.currentStatementType=stype;
        ps.currentStatementState=ParserStatementState::TYPECODE;
    }
    int getConstantID(string word){
        SymbolID ret=pdb.getSymbolID(word);
        if(ret<0 || pdb.symbols[ret].symbolType!=SymbolType::CONSTANT)
            return -1;
        return ret;
    }
    void parseWord(string word,int line) {
        //cout<<toString(getTokenType(word))<<"  "<<word<<"  line  "<<line<<endl;
        if(ps.errorState)
            return;

        TokenType ttype=getTokenType(word);

        if(ps.commentSkip) {
            if(ttype==TokenType::CEND)
                ps.commentSkip=false;
            return;
        }
        switch(ttype) {
case TokenType::CBEGIN: 
            ps.commentSkip=true;
            break;
case TokenType::CEND: 
            parserError("Comment end found outside of comment environment.", line, word);
            break;
case TokenType::FBEGIN: 
            parserError("File inclusion not implemented.", line, word);
            break;
case TokenType::FEND:  
            parserError("File inclusion not implemented.", line, word);
            break;
case TokenType::BBEGIN: 
            if(ps.currentLabel!="") {
                parserError("Blocks cannot be labeled.", line, word);
                break;
            }
            if(ps.parserState!=CurrentParserState::NONE){
                parserError("Cannot be in state " + 
                    toString(ps.parserState)
                    + " while entering block.", line, word);
                break;
            }
            ps.symbolStackLevels.push_back(ps.symbolStackLevels.back());
            ps.statementStackLevels.push_back(ps.statementStackLevels.back());
            break;
case TokenType::BEND:  
            if(ps.currentLabel!="") {
                parserError("Ending block statement cannot be labeled.", line, word);
                break;
            }
            if(ps.parserState!=CurrentParserState::NONE){
                parserError("Cannot be in state " + 
                    toString(ps.parserState)
                    + " while ending block.", line, word);
                break;
            }
            if(ps.symbolStackLevels.size()==1){
                parserError("Cannot end block when not in a block.", line, word);
                break;
            }
            {
                ps.symbolStackLevels.pop_back();
                int sysl = ps.symbolStackLevels.back();
                ps.symbolStack.resize(sysl);

                ps.statementStackLevels.pop_back();
                int stsl = ps.statementStackLevels.back();
                ps.statementStack.resize(stsl);
            }
            break;
case TokenType::CONSTANT:  
            if(ps.currentLabel!="") {
                parserError("Constant Statement cannot have a label.", line, word);
                break;
            }
            if(ps.parserState!=CurrentParserState::NONE){
                parserError("Cannot be in state " + 
                    toString(ps.parserState)
                    + " while starting a constant.", line, word);
                break;
            }
            ps.parserState=CurrentParserState::CONSTANTS;
            break;
case TokenType::VARIABLE:  
            if(ps.currentLabel!="") {
                parserError("Variable Statement cannot have a label.", line, word);
                break;
            }
            if(ps.parserState!=CurrentParserState::NONE){
                parserError("Cannot be in state " + 
                    toString(ps.parserState)
                    + " while starting a variable.", line, word);
                break;
            }
            ps.parserState=CurrentParserState::VARIABLES;
            break;
case TokenType::DISJOINT:  
            parserError("Disjoint variables not implemented.", line, word);
            break;
case TokenType::FLOATING: 
            parseSwitchToStatement(StatementType::FLOATING, line, word);
            break;
case TokenType::ESSENTIAL:
            parseSwitchToStatement(StatementType::ESSENTIAL, line, word);
            break;
case TokenType::AXIOM:     
            parseSwitchToStatement(StatementType::AXIOM, line, word);
            break;
case TokenType::PROOF:     
            parseSwitchToStatement(StatementType::PROOF, line, word);
            break;
case TokenType::END:       
            if(ps.parserState==CurrentParserState::NONE){
                parserError("End statement found while not parsing a statement.", line, word);
                break;
            }
            switch(ps.parserState){
                case CurrentParserState::VARIABLES:
                case CurrentParserState::CONSTANTS:
                    break;
                case CurrentParserState::STATEMENT:
                    //Pretty sure I don't want to change
                    // ps.curentStatementState and ps.currentStatementType,
                    // but might want to do in the future. (Add a NULL enum for example)
                    pushStatement(line,word);
                    // pdb.statements.push_back(ps.currentStatement);
                    // ps.currentStatement=Statement();
                    // ps.statementStack.push_back(pdb.statements.size()-1);
                    // ps.statementStackLevels.back()+=1;
                    break;
                default:
                    break;
            }
            ps.parserState=CurrentParserState::NONE;
            break;
case TokenType::EQUALS:    
            if(ps.parserState!=CurrentParserState::STATEMENT){
                parserError("Symbol must occur inside a proof statement", line, word);
                break;
            }
            if(ps.currentStatementType!=StatementType::PROOF){
                parserError("Symbol must occur inside a proof statement", line, word);
                break;
            }
            if(ps.currentStatementState!=ParserStatementState::SYMBOLS){
                parserError("Typecode missing inside proof statement.", line, word);
                break;
            }
            ps.currentStatementState=ParserStatementState::PROOF;
            break;
case TokenType::TOKEN: 
            /*
            We could be in ps.parserState===NONE, in which case the token
            should be interpreted as a label.
            
            We could be in ps.parserState==VARIABLE or CONSTANT, in which case
            we push the appropriate active variables. Checking for CONSTANT
            only at top level should be done earlier.

            We could be in ps.parserState==STATEMENT, in which case we've gotta
            switch on ps.currentStatementState and ps.currentStatementType to
            handle filling in the appropriate expression.
            */
            switch(ps.parserState){
            case CurrentParserState::NONE:
                if(ps.currentLabel!="") {
                    parserError("Double label encountered.", line, word);
                    break;
                }
                ps.currentLabel=word;
                break;
            case CurrentParserState::VARIABLES:
                {
                    SymbolID symid=pdb.getSymbolID(word);
                    bool symIsActive = (symid!=-1) && symbolIDIsActive(symid);
                    if(symIsActive){
                        parserError("Variable "+word+" already defined and active.", line, word);
                        break;
                    }
                    if(pdb.getStatementID(word)!=-1){
                        parserError("Trying to declare variable, but Statement "+word+" already defined.", line, word);
                        break;
                    }
                    if(symid!=-1) {
                        // We've already checked that the symbol is not active, so we simply 
                        // need to redeclare it, not push it to the pdb.symbols list.
                        ps.symbolStack.push_back(symid);
                        ps.symbolStackLevels.back()+=1;
                    } else {
                        pdb.symbols.push_back(Symbol{word, SymbolType::VARIABLE});
                        ps.symbolStack.push_back(pdb.symbols.size()-1);
                        ps.symbolStackLevels.back()+=1;
                    }
                }
                break;
            case CurrentParserState::CONSTANTS:
                if(pdb.getSymbolID(word)!=-1){
                    parserError("Constant "+word+" already defined.", line, word);
                    break;
                }
                if(pdb.getStatementID(word)!=-1){
                    parserError("Trying to declare constant, but Statement "+word+" already defined.", line, word);
                    break;
                }
                if(ps.symbolStackLevels.size()>1){
                    parserError("Cannot declare constant inside a block.", line, word);
                    break;
                }
                pdb.symbols.push_back(Symbol{word, SymbolType::CONSTANT});
                ps.symbolStack.push_back(pdb.symbols.size()-1);
                ps.symbolStackLevels.back()+=1;
                break;
            case CurrentParserState::STATEMENT:
                switch(ps.currentStatementState){
                case ParserStatementState::TYPECODE:
                    {
                        SymbolID typecode = getConstantID(word);
                        if (typecode == -1)
                        {
                            parserError("Typecode " + word + " not defined as a constant.", line, word);
                            break;
                        }
                        ps.currentStatement.typecode = typecode;
                        ps.currentStatementState = ParserStatementState::SYMBOLS;
                    }
                    break;
                case ParserStatementState::SYMBOLS:
                    {
                        SymbolID id = pdb.getSymbolID(word);
                        if(id==-1){
                            parserError("Symbol "+word+" not defined.", line, word);
                            break;
                        }
                        if(ps.currentStatementType==StatementType::FLOATING
                               && ps.currentStatement.symbols.size()>=1){
                            parserError("Floating hypothesis can only have one symbol.", line, word);
                            break;
                        }
                        if(!isSymbolActive(id)){
                            parserError("Symbol "+word+" not active.", line, word);
                            break;
                        }
                        ps.currentStatement.symbols.push_back(id);
                    }
                    break;
                case ParserStatementState::PROOF:   
                    {
                        StatementID sid = pdb.getStatementID(word);
                        if(sid==-1){
                            parserError("Statement "+word+" not defined.", line, word);
                            break;
                        }
                        if(!isStatementActive(sid)){
                            parserError("Statement "+word+" not active.", line, word);
                            break;
                        }
                        ps.currentStatement.statements.push_back(sid);
                    }
                    break;
                default:
                    break;
                }
                break;
            default:
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

/* Refactor the proof checker:
    ProofStatement typecode, list of math symbols
    ProofStatement has three purposes in life: 
        - Store statements on the proof stack
        - Arguments to the unification function
        - Storing and returning replacement rules
*/
struct ProofStatement {
    SymbolID typecode;
    vector<SymbolID> sym;
    ProofStatement() { } 
    ProofStatement(SymbolID typecode, const vector<SymbolID> sym) : typecode(typecode), sym(sym) { }
    bool equals(const ProofStatement &arg) const {
        bool ret=typecode==arg.typecode;
        ret=ret&&(sym.size()==arg.sym.size());
        int i=0;
        while(ret && i<sym.size()){
            ret=ret&&(sym[i]==arg.sym[i]);
            i++;
        }
        return ret;
    }
    ostream& appendToStream(ostream &arg) {
        arg<<typecode<<" ";
        for(int i=0;i<sym.size();i++){
            arg<<sym[i];
            if(i<sym.size()-1)
                arg<<" ";
        }
        return arg;
    }
    ostream& appendToStream(ostream &arg, ProofDatabase &pdb) {
        arg<<pdb.getSymbol(typecode).label<<" ";
        for(int i=0;i<sym.size();i++){
            arg<<pdb.getSymbol(sym[i]).label;
            if(i<sym.size()-1)
                arg<<" ";
        }
        return arg;
    }
};

struct ReplacementRule {
    SymbolID from;
    vector<SymbolID> to;
    ReplacementRule() { } 
    ReplacementRule(SymbolID from, vector<SymbolID> to) : from(from), to(to) { }

    ostream& appendToStream(ostream &arg) {
        arg<<from<<" ";
        for(int i=0;i<to.size();i++) {
            arg<<to[i];
            if(i<to.size()-1)
                arg<<" ";
        }
        return arg;
    }

    ostream& appendToStream(ostream &arg, ProofDatabase &pdb) {
        arg<<pdb.getSymbol(from).label<<" replace with ";
        for(int i=0;i<to.size();i++){
            arg<<pdb.getSymbol(to[i]).label;
            if(i<to.size()-1)
                arg<<" ";
        }
        return arg;
    }
};

struct Frame {
    vector<ReplacementRule> frame;
    // Look up the symbol "from" in the frame and populate "ret" with the replacement rule.
    // If no replacement rule is found, return the list with only the symbol {from}.
    bool lookup(SymbolID from, vector<SymbolID> &ret) {
        for(auto rule : frame) {
            if(from==rule.from){
                ret=rule.to;
                return true;
            }
        }
        ret=vector<SymbolID>({from});
        return false;
    }
    ostream& appendToStream(ostream &arg) {
        for(int i=0;i<frame.size();i++){
            frame[i].appendToStream(arg<<"  ");
            if(i<frame.size()-1)
                arg<<"\n";
        }
        return arg;
    }
    ostream& appendToStream(ostream &arg, ProofDatabase &pdb) {
        for(int i=0;i<frame.size();i++){
            frame[i].appendToStream(arg<<"  ", pdb);
            if(i<frame.size()-1)
                arg<<"\n";
        }
        return arg;
    }
};

bool applyFrame(const ProofStatement &init, Frame &frame, ProofStatement &ret, ProofDatabase &pdb){
    ret.typecode=init.typecode;
    for(SymbolID id : init.sym) {
        if (pdb.isVariable(id)) {
            vector<SymbolID> newsymbols;
            bool success=frame.lookup(id,newsymbols);
            if(!success)
                return false;
            ret.sym.insert(ret.sym.end(),newsymbols.begin(),newsymbols.end());
        } else {
            ret.sym.push_back(id);
        }
    }
    return true;
}

/* 
Earliest statement (usually a floating hypothesis) will be the last element of
from and to. eg. "to[to.size()-1]" should be the last element popped off the proof stack.
*/
bool unify(Frame &frame,
    vector<ProofStatement> from, 
    vector<StatementType> fromTypes,
    vector<ProofStatement> to, 
    ProofDatabase &pdb) {
    if(from.size()!=to.size()) {
        cerr<<"unify lengths different"<<endl;
        return false;
    }
    for(int i=to.size()-1;i>=0;i--) {
        ProofStatement &fromStatement=from[i];
        ProofStatement &toStatement=to[i];
        if(fromStatement.typecode != toStatement.typecode) {
            cerr<<"Error during unification! Typecode mismatch."<<endl;
            return false;
        }
        if(fromTypes[i]==StatementType::FLOATING) {
            //Two cases, if the symbol isn't in the frame, we add it.
            //Else, if it is in the frame, we check that the replacement is consistent.
            vector<SymbolID> lresult;
            bool success=frame.lookup(fromStatement.sym.at(0), lresult);
            if(success){
                if(!toStatement.equals(ProofStatement(fromStatement.typecode,lresult))){
                    cerr<<"Error during unification! Symbol list mismatch."<<endl;
                    return false;
                }
            } else {
                frame.frame.push_back(
                    ReplacementRule(fromStatement.sym.at(0),
                                    toStatement.sym));
            }
        } else {
            // Else it's a mandatory essential hypothesis, and cannot define a new replacement rule
            // Instead, we just have to check for consistency.
            ProofStatement ret;
            bool success=applyFrame(fromStatement, frame,ret, pdb);
            if(!success) {
                cerr << "Error during unification! Mandatory hypothesis contains variable with no substitution."<<endl;
                return false;
            }
            success = toStatement.equals(ret);
            if(!success) {
                cerr << "Error during unification! Mandatory hypothesis mismatches statement on proof stack after replacement!"<<endl;
                return false;
            }
        }
    }
    return true;
}

/*ostream &appendToStream(ostream &arg, const vector<ProofStatement> &list, ProofDatabase &pdb){
    for(int i=0;i<list.size();i++){
        list[i].appendToStream(arg<<"  ", pdb);
        if(i<list.size()-1)
            arg<<"\n";
    }
    return arg;
}*/
ostream &appendToStream(ostream &arg, const vector<SymbolID> &list, ProofDatabase &pdb){
    for(int i=0;i<list.size();i++){
        arg<<pdb.getSymbol(list[i]).label;
        if(i<list.size()-1)
            arg<<" ";
    }
    return arg;
}

ostream &appendToStream(ostream &arg, const Statement &stat, ProofDatabase &pdb){
    // Print the statement, excluding proof's "$= ...", in the form "$a typecode symbols $."
    if(stat.statementType==StatementType::FLOATING){
        arg<<stat.label<<" $f "<<pdb.getSymbol(stat.typecode).label<<" ";
        appendToStream(arg, stat.symbols, pdb)<<" $.";
    } else if(stat.statementType==StatementType::ESSENTIAL){
        arg<<stat.label<<" $e "<<pdb.getSymbol(stat.typecode).label<<" ";
        appendToStream(arg, stat.symbols, pdb)<<" $.";
    } else if(stat.statementType==StatementType::AXIOM){
        arg<<stat.label<<" $a "<<pdb.getSymbol(stat.typecode).label<<" ";
        appendToStream(arg, stat.symbols, pdb)<<" $.";
    } else if(stat.statementType==StatementType::PROOF){
        arg<<stat.label<<" $p "<<pdb.getSymbol(stat.typecode).label<<" ";
        appendToStream(arg, stat.symbols, pdb)<<" $.";
    }
    return arg;
}


bool checkProof(Statement &proof, ProofDatabase &pdb) {
    if(proof.statementType!=StatementType::PROOF) {
        cerr<<"Not a proof."<<endl;
        return false;
    }
    vector<StatementID> &proofcommands = proof.statements;
    ProofStatement target(proof.typecode,proof.symbols);
    vector<ProofStatement> proofstack;
    for(size_t n_command=0; n_command<proofcommands.size();n_command++) {
//#ifdef VERBOSE
        //cout<<"\n";
//#endif
        StatementID foo=proofcommands[n_command];
        Statement &proofcommand = pdb.getStatement(foo);
        // If it's a hypothesis, we just push it to the stack
        if(proofcommand.statementType==StatementType::ESSENTIAL
            || proofcommand.statementType == StatementType::FLOATING) {
            ProofStatement mynew(proofcommand.typecode,proofcommand.symbols);
#ifdef VERBOSE
            if(proofcommand.statementType == StatementType::ESSENTIAL)
                mynew.appendToStream(cout<<"Pushing to stack: ",pdb)<<endl;
            else 
                mynew.appendToStream(cout<<"Pushing to stack: ",pdb)<<endl;
#endif
            proofstack.push_back({proofcommand.typecode,proofcommand.symbols});
            continue;
        }

        // If it's an assertion, we need to do unification among the mandatory
        // hypotheses, and things we pop from the stack.
        /* Everything in the list of mandatory hypotheses and foo.symbols gets
        relabeled, then the mandatory hypotheses are unified with things popped from
        the stack. Then, foo.symbols is replaced according to the unficiation, and
        pushed to the stack. */
        vector<ProofStatement> mandatory;
        vector<StatementType> mandatoryTypes;
        vector<ProofStatement> popped;
        for(int i=proofcommand.mandatory.size()-1;i>=0;i--) {
            Statement &myMandatory = pdb.getStatement(proofcommand.mandatory[i]);
            mandatory.push_back({myMandatory.typecode,myMandatory.symbols});
            mandatoryTypes.push_back(myMandatory.statementType);
            if(proofstack.size()==0) {
                cerr << "Error: proof command " << proofcommand.label 
                    << " requires mandatory hypothesis " 
                    << myMandatory.label 
                    << ", but proof stack is empty." << endl;
                return false;
            }
            popped.push_back(proofstack.back());
            proofstack.pop_back();
        }
#ifdef VERBOSE
        if(mandatory.size()>0 || popped.size()>0) {
            cout<<"\n";
            appendToStream(cout<<"Parsing statement ", proofcommand, pdb)<<endl;
            cout<<"Mandatory hypotheses: "<<endl;
            for(int i=0;i<mandatory.size();i++){
                mandatory[i].appendToStream(cout<<"  ",pdb)<<endl;
            }
            cout<<"Popped from stack: "<<endl;
            for(int i=0;i<popped.size();i++){
                popped[i].appendToStream(cout<<"  ",pdb)<<endl;
            }
        }
#endif
        Frame frame;
        bool success=unify(frame, mandatory, mandatoryTypes, popped, pdb);
        if(!success){
            cerr << "Error in proof command " << proofcommand.label 
                << ". Unable to unify proof stack while parsing command " 
                << n_command << " with label "
                << proofcommand.label
                << "." << endl;
            return false;
        }

#ifdef VERBOSE
        if(frame.frame.size()>0){
            cout<<"Unifying Frame: "<<endl;
            frame.appendToStream(cout, pdb)<<endl;
        }
#endif

        ProofStatement replaced;
        success=applyFrame(ProofStatement(proofcommand.typecode,proofcommand.symbols),
                    frame,replaced,pdb);
        if(!success){
            cerr << "Error in proof command " << proofcommand.label 
                 << ". Unification succeeded, but unsubstituted variables are left over." <<endl;
            return false;
        }
#ifdef VERBOSE
        replaced.appendToStream(cout<<"Pushing to stack: ", pdb)<<endl;
#endif
        proofstack.push_back(replaced);
    }
    if(proofstack.size()!=1) {
        cerr << "Error in proof " << proof.label 
             << ". Reached end of proof stack, but proof stack size differs from 1 element!!" <<endl;
        return false;
    }
    if(!proofstack[0].equals(target)){
        cerr << "Error in proof " << proof.label 
             << ". Reached end of proof stack, but final statements disagree!" <<endl;
        cerr<<"stack:  ";
        proofstack[0].appendToStream(cerr, pdb)<<endl;
        cerr<<"target: ";
        target.appendToStream(cerr,pdb)<<endl;
        return false;
    }
    return true;
}

void checkProofs(ProofDatabase &pdb){
    bool valid=true;
    for(int i=0; i<pdb.statements.size(); i++){
        Statement &stat=pdb.statements[i];
        if(stat.statementType!=StatementType::PROOF)
            continue;
        valid=valid && checkProof(stat,pdb);
        if(!valid){
            cerr<<"Error at proof oh no 🥵🥵🥵🥵🥵🥵🥵🥵"<<endl;
            return;
        }
    }
    cout<<"Proof checking succeeded! Yippee!"<<endl;
}



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
            if(ts==TokenizerState::ACCUMULATING){
                ts=TokenizerState::WHITESPACE;
                mm.parseWord(identifier,line);
            }
            if(c=='\r'||c=='\n'){
                line++;
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

    mm.pdb.printDatabase();
    checkProofs(mm.pdb);
    cout<<"Done!"<<endl;
    return 0;
}












