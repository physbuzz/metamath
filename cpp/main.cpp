#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <cctype>
#include <vector>
#include <memory>
#include <algorithm>
#include <set>

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

struct MathSymbolString {
    std::vector<int> str;
    MathSymbolString() : str() { }
    MathSymbolString(std::vector<int> str) : str(str) { 
    }
};

struct Replacement {
    SymbolID from;
    vector<SymbolID> to;
};


// ReplacementList can also be referred to as a Frame.
class ReplacementList {
public:
    vector<Replacement> rules;
    vector<SymbolID> replace(SymbolID arg, bool noerror=true){
        for(auto rule : rules){
            if(rule.from==arg)
                return rule.to;
        }
        if(!noerror) { // :)
             // >:)
            cerr << "No match found in replacement rule."<<endl;
        }
        return vector<SymbolID>({arg});
    }
    MathSymbolString replace(MathSymbolString arg, bool noerror=true){
        MathSymbolString ret;
        for(auto item : arg.str){
            auto list=replace(item,noerror);
            for(auto replaced : list)
                ret.str.push_back(replaced);
        }
        if(!noerror) { // :)
             // >:)
            cerr << "No match found in replacement rule."<<endl;
        }
        return ret;
    }
    MathSymbolString replaceVariables(MathSymbolString arg, ProofDatabase &pdb, bool noerror=true){
        MathSymbolString ret;
        for(auto item : arg.str){
            Symbol sym=pdb.symbols.at(item);
            if(sym.symbolType==SymbolType::VARIABLE){
                auto list=replace(item,noerror);
                for(auto replaced : list)
                    ret.str.push_back(replaced);
            } else {
                ret.str.push_back(item);
            }
        }
        return ret;
    }
};

bool unify(
        ReplacementList &ret,
        vector<MathSymbolString> from, 
        vector<MathSymbolString> to, 
        ProofDatabase &pdb){
    // check lengths
    if(from.size() != to.size()){
        cerr<<"Cannot unify: from and to list lengths are not identical"<<endl;
        return false;
    }
    for(int i=from.size(); i>=0; i--) {
        
    }
    return true;
}

void checkProofs(ProofDatabase &pdb){
    for(int i=0; pdb.statements.size(); i++){
        if(pdb.statements[i].statementType==StatementType::PROOF){
            Statement &proof=pdb.statements[i];
            std::vector<StatementID> &proofcommands=pdb.statements[i].statements;
            MathSymbolString target(pdb.statements[i].symbols);
            vector<MathSymbolString> proofstack;
            for(StatementID foo : proofcommands) {
                Statement &proofcommand=pdb.statements[foo];
                // If it's a hypothesis, we just push it to the stack
                if(proofcommand.statementType==StatementType::ESSENTIAL
                    || proofcommand.statementType==StatementType::FLOATING) {
                    proofstack.push_back(proofcommand.symbols);
                } else {
                    // If it's an assertion, we need to do unification among the mandatory 
                    // hypotheses, and things we pop from the stack.
                    /* Everything in the list of mandatory hypotheses and foo.symbols gets 
                    relabeled, then the mandatory hypotheses are unified with things popped from 
                    the stack. Then, foo.symbols is replaced according to the unficiation, and 
                    pushed to the stack. */

                    vector<MathSymbolString> mandatory;
                    vector<MathSymbolString> popped;
                    for(int i=proofcommand.mandatory.size();i>=0;i--) {
                        StatementID mandatoryID=proofcommand.mandatory[i];
                        mandatory.push_back(pdb.statements.at(mandatoryID).symbols);
                        if(proofstack.size()==0) {
                            cerr<<"Error: proof command "<<proofcommand.label<<" requires mandatory hypothesis "<<pdb.statements.at(mandatoryID).label<<", but proof stack is empty."<<endl;
                            return;
                        }
                        popped.push_back(proofstack.back());
                        proofstack.pop_back();
                    }
                    ReplacementList rl = unify(mandatory, popped);

                }
            }
        }
    }
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
    return 0;
}












