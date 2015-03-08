/***************************************************************************************************
*                                                                                                  *
*                                        Lògica a la Informàtica                                   *
*                                                                                                  *
*                                              SAT-SOLVER                                          *
*                                                                                                  *
****************************************************************************************************
*                                                                                                  *
*                                         Arnau Sangrà Rocamora                                    *
*                                                                                                  *
****************************************************************************************************
*                                                                                                  *
*                                                                                                  *
***************************************************************************************************/

/*  TODO:
    -Change penalisation increment || divide penalisations after certain interval
    */


#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>

#include <time.h> 

using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;



/**************************************************************************************************/
// OwnStructuresDefined:
double t_begin;
double t_end;
int updateInterval;

vector<vector<int> > clausesOnTrue;
vector<vector<int> > clausesOnNegative;

vector<int> conflictsTrueLiterals;
vector<int> conflictsFalseLiterals;

/**************************************************************************************************/
// OwnFunctions:
void updateConflictsHeuristic (int lit) {

    if(lit == 0) cout << "LIT == 0 on updateConflictsHeuristic :(" << endl;
    if(lit > 0) {
        cout << "UPDATING LITERAL:" << lit << endl; 
         ++conflictsTrueLiterals[lit];
    }
    else {
        cout << "UPDATING LITERAL:" << lit << endl; 
        ++conflictsFalseLiterals[-lit];
    }
}

void checkInitConflictVectors () {
    bool allright = true;
    cout << "@Activity Penalisation Literals" << endl << "T.size: " << conflictsTrueLiterals.size() << " content zero: ";
    for (int i = 0; i < conflictsTrueLiterals.size(); ++i) {
        if(conflictsTrueLiterals[i] != 0) allright = false;
    }
    if(allright) cout << "true" << endl;
    else {
        cout << "false" << endl;
        allright = true;
    }
    cout << "F.size: " << conflictsFalseLiterals.size() << ", content zero: ";
    for (int i = 0; i < conflictsFalseLiterals.size(); ++i) {
            if(conflictsFalseLiterals[i] != 0) allright = false;
        }
    if(allright) cout << "true" << endl;
    else {
        cout << "false" << endl;
        allright = true;
    }
}


void checkConflictVectorsContent () {
    int max = 0;
    cout << "conflictsTrueLiterals:" << endl;
    for (int i = 0; i < conflictsTrueLiterals.size(); ++i) {
        cout << "L" << i << ": " << conflictsTrueLiterals[i] << ", ";
        if (conflictsTrueLiterals[i] >= conflictsTrueLiterals[max]) max = i;
    }
    cout << endl << cout << "\tmostConflictiveTrue: " << max << endl << "conflictsFalseLiterals:" << endl;
    max = 0;
    for (int i = 0; i < conflictsFalseLiterals.size(); ++i) {
        cout << "lit" << i << ": " << conflictsFalseLiterals[i] << ", ";
        if(conflictsFalseLiterals[i] >= conflictsFalseLiterals[max]) max = i;
    }
    cout << endl << "\tmostConflictiveFalse: " << max << endl;
}



/**************************************************************************************************/


int currentValueInModel (int lit) {
    //POST: returns the most conflictive literal
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
    }
}


int getTrueLiteralMostConflictive() {
    //POST: returns the most conflictive negated literal
    int max = 0;
    for(int i = 1; i < numVars+1; ++i) {
        if(conflictsTrueLiterals[i] >= conflictsTrueLiterals[max] and currentValueInModel(i) == UNDEF) {
            max = i;
        }
    }
    //cout << "MAX TRUE: " << max << endl;
    return max;
}


int getFalseLiteralMostConflictive() {
    int max = 0;
    for (int i = 1; i < numVars+1; ++i) {
        if(conflictsFalseLiterals[i] >= conflictsFalseLiterals[max] and currentValueInModel(i) == UNDEF) {
            max = i;
        }
    }
    //cout <<  "MAX FALSE: " << max << endl;
    return max;
}


int getMostConflictive () {
    //POST: returns the most conflictive (pos/neg) literal according its activity score.
    // tries to detect most conflictive literals earlier.

    //DEBUG INFO:
    //checkConflictVectorsContent();
    int t = getTrueLiteralMostConflictive();
    //cout << "1:" << t << endl;
    int f = getFalseLiteralMostConflictive();
    //cout << "2:" << f << endl;
    if(conflictsTrueLiterals[t] > conflictsFalseLiterals[f]) return t;
    else return -f;
}

void readClauses () {
    // Skip comments
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }
    // Read "cnf numVars numClauses"
    string aux;
    cin >> aux >> numVars >> numClauses;
    clauses.resize(numClauses);

    clausesOnTrue.resize(numVars+1);
    clausesOnNegative.resize(numVars+1);
    // cout << numVars << "; " << clausesOnTrue.size() << ", " << clausesOnNegative.size() << endl;

    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            clauses[i].push_back(lit);
            if(lit > 0) clausesOnTrue[lit].push_back(i);
            else clausesOnNegative[-lit].push_back(i);
        }
    }
}


void setLiteralToTrue(int lit){
    modelStack.push_back(lit);
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;
}


bool propagateGivesConflict () {
  while(indexOfNextLitToPropagate < modelStack.size()) {
        ++indexOfNextLitToPropagate;

        cout << "modelStack dump: ";
        for(int i = 0; i < modelStack.size(); ++i) cout << modelStack[i] << " ";
        cout << endl;

        //replace with check only affected clauses
        cout << "modelStack.size(): " << modelStack.size() << ", accessing to: " << modelStack.size()-1 << endl;
        int literalToCheck = modelStack[modelStack.size()-1];
        
        if(literalToCheck > 0) {
            cout << "literalToCheck: " << literalToCheck << endl;
            cout << "checking inside clausesOnNegative" << endl;
            cout << clausesOnTrue[-literalToCheck].size() << " clauses to check" << endl;
            for(int i = 0; i < clausesOnNegative[literalToCheck].size(); ++i) {
                bool someLitTrue = false;
                int numUndefs = 0;
                int lastLitUndef = 0;
                int c = clausesOnNegative[literalToCheck][i];
                cout << "more specifically, c = clause num:" << c << endl;

                for(int j = 0; not someLitTrue and j < clauses[c].size(); ++j) {
                    int val = currentValueInModel(clauses[c][j]);
                    if(val == TRUE) someLitTrue = true;
                    else if (val == UNDEF) {
                        ++numUndefs;
                        lastLitUndef = clauses[c][j];
                    }
                }
                if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
                else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
            }
        }
        else {
            cout << "literalToCheck: " << literalToCheck << endl;
            cout << "checking inside clausesOnTrue" << endl;
            cout << clausesOnTrue[-literalToCheck].size() << " clauses to check" << endl;
            for(int i = 0; i < clausesOnTrue[-literalToCheck].size(); ++i) {
                bool someLitTrue = false;
                int numUndefs = 0;
                int lastLitUndef = 0;
                int c = clausesOnTrue[-literalToCheck][i];
                cout << "more specifically, c = clause num:" << c << endl;

                for(int j = 0; not someLitTrue and j < clauses[c].size(); ++j) {
                    int val = currentValueInModel(clauses[c][j]);
                    if(val == TRUE) someLitTrue = true;
                    else if (val == UNDEF) {
                        ++numUndefs;
                        lastLitUndef = clauses[c][j];
                    }
                }
                if (not someLitTrue and numUndefs == 0) {
                    cout << "CONFLICT DETECTED" << endl;
                    return true; // conflict! all lits false  
                } 
                else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
            }
        }



        // for(uint i = 0; i < numClauses; ++i) {
        //     bool someLitTrue = false;
        //     int numUndefs = 0;
        //     int lastLitUndef = 0;
        //     for(uint k = 0; not someLitTrue and k < clauses[i].size(); ++k) {
        //         int val = currentValueInModel(clauses[i][k]);
        //         if (val == TRUE) someLitTrue = true;
        //         else if (val == UNDEF) {
        //             ++numUndefs;
        //             lastLitUndef = clauses[i][k];
        //         }
        //     }
        //     if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
        //     else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
        // }


    }
    return false;
}


void backtrack(){
    uint i = modelStack.size() -1;
    int lit = 0;
    while(modelStack[i] != 0) { // 0 is the DL mark
        lit = modelStack[i];
        model[abs(lit)] = UNDEF;
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
  
    indexOfNextLitToPropagate = modelStack.size();

    //update penalisation
    updateConflictsHeuristic(lit);
    setLiteralToTrue(-lit);  // reverse last decision
}

//************************************************* Heuristic for finding the next decision literal:
int getNextDecisionLiteral(){
    // TODO: improve with division of penalisations after certain time:
    //                                  ->reduce effect of earlier penalisations made.
    return getMostConflictive();
    // for (uint i = 1; i <= numVars; ++i) // stupid heuristic:
    //     if (model[i] == UNDEF) return i;  // returns first UNDEF var, positively
    // return 0; // reurns 0 when all literals are defined
}

void checkmodel () {
    for(int i = 0; i < numClauses; ++i) {
        bool someTrue = false;
        for(int j = 0; not someTrue and j < clauses[i].size(); ++j) {
            someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
        }
        if (not someTrue) {
            cout << "Error in model, clause is not satisfied:";
            for (int j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
                cout << endl;
            exit(1);
        }
    }
}


/**************************************************************************************************/


int main(){ 
    t_begin = clock();
    readClauses(); // reads numVars, numClauses and clauses
    model.resize(numVars+1,UNDEF);
    indexOfNextLitToPropagate = 0;  
    decisionLevel = 0;

    // Take care of initial unit clauses, if any
    for (uint i = 0; i < numClauses; ++i) {
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = currentValueInModel(lit);
            if (val == FALSE) {cout << "UNSATISFIABLE" << endl; return 10;}
            else if (val == UNDEF) setLiteralToTrue(lit);
        }
    }

    //initLiteralsPenalisationIndexs
    conflictsTrueLiterals.resize(numVars+1, 0);
    conflictsFalseLiterals.resize(numVars+1, 0);
    // checkInitConflictVectors();
    
      // DPLL algorithm
    while(true) {
        while(propagateGivesConflict()) {
            if(decisionLevel == 0) {
                cout << "UNSATISFIABLE" << endl;
                t_end = clock();
                cout << "TIME ELAPSED: " << ((t_end - t_begin) / CLOCKS_PER_SEC) << endl;
                return 10;
            }
            backtrack();
        }
        int decisionLit = getNextDecisionLiteral();
        if (decisionLit == 0) {
            checkmodel();
            cout << "SATISFIABLE" << endl;
            t_end = clock();
            cout << "TIME ELAPSED: " << ((t_end - t_begin) / CLOCKS_PER_SEC) << endl;
            return 20;
        }
        // start new decision level:
        modelStack.push_back(0);  // push mark indicating new DL
        ++indexOfNextLitToPropagate;
        ++decisionLevel;
        setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
    }
}