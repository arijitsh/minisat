
/************************************=== CCAnr
 *===***************************************
 ** CCAnr is a local search solver for the Boolean Satisfiability (SAT) problem,
 ** which is especially designed for non-random instances.
 ** CCAnr is designed and implemented by Shaowei Cai (email:
 *shaoweicai.cs@gmail.com),
 *****************************************************************************************/

/*****************************=== Develpment history
===*************************************
** 2011.5
** SWCC (Smoothed Weighting and Configuration Checking) by Shaowei Cai
** New Idea: Configuration Checking (CC)
** A variable is configuration changed, if since its last flip, at least one of
its
** neighboring var has been flipped.
** In the greedy mode, Swcc picks the best Configuration Changed Decreasing  var
to flip.
** In the random mode, it updates weights, and flips the oldest var in a random
unsat clause.

** 2011.9
** SWCCA (Smoothed Weighting and Configuration Checking with Aspiration) by
Shaowei Cai
** New Idea: CC with Aspiration (CCA)
** Modification: in greedy mode, it first prefers to flip the best CCD var. If
there is
** no CCD variable, then flip the best significant decreasing var, i.e., with a
great
** positive score (in Swcca, bigger than averaged clause weight), if there exsit
such vars.

** 2013.4
** CCAnr (CCA for non-random SAT)
** Modifications: Generalize the smoothig fomula as w(ci)=w(ci)*p+ave_w*q; pick
the greediest
** variable in the diversification mode.
************************************************************************************************/

#ifndef _CCA_H_
#define _CCA_H_

// #include "basis.h"

#define pop_s(stack) stack[--stack##_fill_pointer]
#define push_s(item, stack) stack[stack##_fill_pointer++] = item


/* limits on the size of the problem. */
#define MAX_VARS 4000010
#define MAX_CLAUSES 20000000

#define sigscore ave_weight
// #include "cw.h"
// #include "preprocessor.h"

#include <string.h>
#include <sys/times.h> //these two h files are for linux
#include <unistd.h>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>
#include "minisat/core/Solver.h"
#include "minisat/mtl/Vec.h"

using namespace std;
using namespace Minisat;

class CCAnr
{
   public:
       ~CCAnr();

    char *inst;
    int seed;

    long long ls_no_improv_times;

    bool aspiration_active;

    // Define a data structure for a literal in the SAT problem.
    struct lit {
        int clause_num; // clause num, begin with 0
        int var_num;    // variable num, begin with 1
        int sense;      // is 1 for true literals, 0 for false literals.
    };
    enum type { SAT3, SAT5, SAT7, strSAT } probtype;

   public:
    /*parameters of the instance*/
    int num_vars;    // var index from 1 to num_vars
    int num_clauses; // clause index from 0 to num_clauses-1
    int max_clause_len;
    int min_clause_len;
    int formula_len = 0;
    double avg_clause_len;
    double ratio;

    /* literal arrays */
    lit *var_lit[MAX_VARS];            // var_lit[i][j] means the j'th literal of var i.
    int var_lit_count[MAX_VARS];       // amount of literals of each var
    vector<lit*> clause_lit;      // clause_lit[i][j] means the j'th literal of
                                       // clause i.
    int clause_lit_count[MAX_CLAUSES]; // amount of literals in each clause
    int simplify = 0;

    /* Information about the variables. */
    int score[MAX_VARS];
    int time_stamp[MAX_VARS];
    int conf_change[MAX_VARS];
    int *var_neighbor[MAX_VARS];
    int var_neighbor_count[MAX_VARS];
    // int		pscore[MAX_VARS];
    int fix[MAX_VARS];

    /* Information about the clauses */
    int clause_weight[MAX_CLAUSES];
    int sat_count[MAX_CLAUSES];
    int sat_var[MAX_CLAUSES];
    // int		sat_var2[MAX_CLAUSES];

    // unsat clauses stack
    int unsat_stack[MAX_CLAUSES]; // store the unsat clause number
    int unsat_stack_fill_pointer;
    int index_in_unsat_stack[MAX_CLAUSES]; // which position is a clause in the
                                           // unsat_stack

    int this_try_best_unsat_stack_fill_pointer;

    // variables in unsat clauses
    int unsatvar_stack[MAX_VARS];
    int unsatvar_stack_fill_pointer;
    int index_in_unsatvar_stack[MAX_VARS];
    int unsat_app_count[MAX_VARS]; // a varible appears in how many unsat clauses

    // configuration changed decreasing variables (score>0 and confchange=1)
    int goodvar_stack[MAX_VARS];
    int goodvar_stack_fill_pointer;
    int already_in_goodvar_stack[MAX_VARS];

    // unit clauses preprocess
    lit unitclause_queue[MAX_VARS];
    int unitclause_queue_beg_pointer = 0;
    int unitclause_queue_end_pointer = 0;
    int clause_delete[MAX_CLAUSES];

    /* Information about solution */
    int cur_soln[MAX_VARS]; // the current solution, with 1's for True variables,
                            // and 0's for False variables

    // cutoff
    int max_tries = 0; // Arijit  : Set for CDCL call.
    int tries;
    int max_flips = 2000000000;
    int step;
    int verbosity;
    // the following [1] elements were made global
    // from local to the function build_instance

    // [1] ends here

    // void setup_datastructure();
    // void free_memory();
    // int build_instance(char *filename);
    // void build_neighbor_relation();

    void free_memory();

    /*
   * Read in the problem.
   */
    int temp_lit[MAX_VARS]; // the max length of a clause can be MAX_VARS

    void build_neighbor_relation();

    int add_clauses(Solver* s, vec<CRef>& clauses, int offs);
    void build_instance_from_solver(Solver* s );
    void print_problem();

    void print_solution();
    int verify_sol();

    int pick_var(void);
    void settings();

    void local_search(long long no_improv_times);

    void default_settings();
    bool parse_arguments(int argc, char **argv);

    inline void unsat(int clause);

    inline void sat(int clause);
    // initiation of the algorithm
    void init(int *soln);

    void flip(int flipvar);
    int run(int *soln, int seedp);
    void unit_propagation();

    void preprocess();

    int ave_weight = 1;
    int delta_total_weight = 0;

    /**************************************** clause weighting for 3sat
   * **************************************************/

    int threshold;
    float p_scale; // w=w*p+ave_w*q
    float q_scale = 0;
    int scale_ave; // scale_ave==ave_weight*q_scale

    int q_init = 0;

    void smooth_clause_weights();

    void update_clause_weights();

    void set_clause_weighting();

}; // end class ccanr

inline CCAnr::~CCAnr() {
    free_memory();
}


#endif
