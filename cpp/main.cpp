#include <iostream>
#include <fstream>
#include <string>
#include <sstream>


using namespace std;

#define MAX_CHAR 256

void help(){
    cout<<"Here is where I'd put a help file...\rIF I HAD ONE!!!"<<endl;
}

enum ParserState{

};

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



main(int argc, char** argv){
    if(argc<2){
        help();
        return 1;
    }
    
    ifstream file(argv[1]);

    if(!file){
        cerr<<"Couldn't open file :'("<<endl;
        return 1;
    }


    string word;
    while( file>>word){
        cout<<toString(getStatementType(word))<<"  "<<word<<endl;
    }

    return 0;
}












