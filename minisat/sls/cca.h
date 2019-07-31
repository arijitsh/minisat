
/************************************=== CCAnr ===***************************************
 ** CCAnr is a local search solver for the Boolean Satisfiability (SAT) problem,
 ** which is especially designed for non-random instances.
 ** CCAnr is designed and implemented by Shaowei Cai (email: shaoweicai.cs@gmail.com),
 *****************************************************************************************/

/*****************************=== Develpment history ===*************************************
** 2011.5
** SWCC (Smoothed Weighting and Configuration Checking) by Shaowei Cai
** New Idea: Configuration Checking (CC)
** A variable is configuration changed, if since its last flip, at least one of its
** neighboring var has been flipped.
** In the greedy mode, Swcc picks the best Configuration Changed Decreasing  var to flip.
** In the random mode, it updates weights, and flips the oldest var in a random unsat clause.

** 2011.9
** SWCCA (Smoothed Weighting and Configuration Checking with Aspiration) by Shaowei Cai
** New Idea: CC with Aspiration (CCA)
** Modification: in greedy mode, it first prefers to flip the best CCD var. If there is
** no CCD variable, then flip the best significant decreasing var, i.e., with a great
** positive score (in Swcca, bigger than averaged clause weight), if there exsit such vars.

** 2013.4
** CCAnr (CCA for non-random SAT)
** Modifications: Generalize the smoothig fomula as w(ci)=w(ci)*p+ave_w*q; pick the greediest
** variable in the diversification mode.
************************************************************************************************/


#ifndef _CCA_H_
#define _CCA_H_

// #include "basis.h"

#define pop_s(stack) stack[--stack ## _fill_pointer]
#define push_s(item, stack) stack[stack ## _fill_pointer++] = item

enum type {SAT3, SAT5, SAT7, strSAT} probtype;

/* limits on the size of the problem. */
#define MAX_VARS    4000010
#define MAX_CLAUSES 20000000


#define sigscore	ave_weight
// #include "cw.h"
// #include "preprocessor.h"

#include <string.h>
#include <sys/times.h> //these two h files are for linux
#include <unistd.h>
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>

using namespace std;

class CCAnr {

public:
    //CCAnr();
    ~CCAnr();
    char * inst;
    int seed;

    long long ls_no_improv_times;

    bool aspiration_active;

// Define a data structure for a literal in the SAT problem.
    struct lit {
        int clause_num;		//clause num, begin with 0
        int var_num;		//variable num, begin with 1
        int sense;			//is 1 for true literals, 0 for false literals.
    };

public:
    /*parameters of the instance*/
    int     num_vars;		//var index from 1 to num_vars
    int     num_clauses;	//clause index from 0 to num_clauses-1
    int		max_clause_len;
    int		min_clause_len;
    int		formula_len=0;
    double	avg_clause_len;
    double 	ratio;

    /* literal arrays */
    lit*	var_lit[MAX_VARS];				//var_lit[i][j] means the j'th literal of var i.
    int		var_lit_count[MAX_VARS];        //amount of literals of each var
    lit*	clause_lit[MAX_CLAUSES];		//clause_lit[i][j] means the j'th literal of clause i.
    int		clause_lit_count[MAX_CLAUSES]; 	// amount of literals in each clause

    lit*	org_clause_lit[MAX_CLAUSES];		//clause_lit[i][j] means the j'th literal of clause i.
    int		org_clause_lit_count[MAX_CLAUSES]; 	// amount of literals in each clause
    int		simplify=0;

    /* Information about the variables. */
    int     score[MAX_VARS];
    int		time_stamp[MAX_VARS];
    int		conf_change[MAX_VARS];
    int*	var_neighbor[MAX_VARS];
    int		var_neighbor_count[MAX_VARS];
//int		pscore[MAX_VARS];
    int		fix[MAX_VARS];


    /* Information about the clauses */
    int     clause_weight[MAX_CLAUSES];
    int     sat_count[MAX_CLAUSES];
    int		sat_var[MAX_CLAUSES];
//int		sat_var2[MAX_CLAUSES];

//unsat clauses stack
    int		unsat_stack[MAX_CLAUSES];		//store the unsat clause number
    int		unsat_stack_fill_pointer;
    int		index_in_unsat_stack[MAX_CLAUSES];//which position is a clause in the unsat_stack

    int		this_try_best_unsat_stack_fill_pointer;

//variables in unsat clauses
    int		unsatvar_stack[MAX_VARS];
    int		unsatvar_stack_fill_pointer;
    int		index_in_unsatvar_stack[MAX_VARS];
    int		unsat_app_count[MAX_VARS];		//a varible appears in how many unsat clauses

//configuration changed decreasing variables (score>0 and confchange=1)
    int		goodvar_stack[MAX_VARS];
    int		goodvar_stack_fill_pointer;
    int		already_in_goodvar_stack[MAX_VARS];

//unit clauses preprocess
    lit		unitclause_queue[MAX_VARS];
    int		unitclause_queue_beg_pointer=0;
    int     unitclause_queue_end_pointer=0;
    int     clause_delete[MAX_CLAUSES];

    /* Information about solution */
    int             cur_soln[MAX_VARS];	//the current solution, with 1's for True variables, and 0's for False variables

//cutoff
    int		max_tries = 0; //Arijit  : Set for CDCL call.
    int		tries;
    int		max_flips = 2000000000;
    int		step;

    int     verbosity;
// the following [1] elements were made global
// from local to the function build_instance

// [1] ends here

// void setup_datastructure();
// void free_memory();
// int build_instance(char *filename);
// void build_neighbor_relation();

    void free_memory()
    {
        int i;
        for (i = 0; i < num_clauses; i++)
        {
            delete[] clause_lit[i];
        }

        for(i=1; i<=num_vars; ++i)
        {
            delete[] var_lit[i];
            delete[] var_neighbor[i];
        }
    }

    /*
     * Read in the problem.
     */
    int temp_lit[MAX_VARS]; //the max length of a clause can be MAX_VARS
    int build_instance(char *filename)
    {

        char    line[1000000];
        char    tempstr1[10];
        char    tempstr2[10];
        int     cur_lit;
        int     i,j;
        int		v,c;//var, clause

        //     free_memory();
        if(verbosity>1)cout << "c [CCAnr] Building Instance" <<endl;
        if(verbosity>1)std::cout<<"c [CCAnr] Initialized with "<< filename <<std::endl;

        ifstream infile(filename);
        if(!infile)    //Arijit : Not Sure, changed infile==NULL to !infile
            return 0;

        /*** build problem data structures of the instance ***/
        infile.getline(line,1000000);
        while (line[0] != 'p')
            infile.getline(line,1000000);

        sscanf(line, "%s %s %d %d", tempstr1, tempstr2, &num_vars, &num_clauses);
        ratio = double(num_clauses)/num_vars;

        if(num_vars>=MAX_VARS || num_clauses>=MAX_CLAUSES)
        {
            cout<<"the size of instance exceeds out limitation, please enlarge MAX_VARS and (or) MAX_CLAUSES."<<endl;
            exit(-1);
        }


// 	cout <<"ac Instance: Number of variables = "<< num_vars <<endl;
// 	cout <<"ac IInitialized with file "<< filename <<endl;

        for (c = 0; c < num_clauses; c++)
        {
            clause_lit_count[c] = 0;
            clause_delete[c] = 0;
        }
        for (v=1; v<=num_vars; ++v)
        {
            var_lit_count[v] = 0;
            fix[v] = 0;
        }

        max_clause_len = 0;
        min_clause_len = num_vars;

        //Now, read the clauses, one at a time.
        for (c = 0; c < num_clauses; c++)
        {
            infile>>cur_lit;

            while (cur_lit != 0) {
                temp_lit[clause_lit_count[c]] = cur_lit;
                clause_lit_count[c]++;

                infile>>cur_lit;
            }
            clause_lit[c] = new lit[clause_lit_count[c]+1];

            for(i=0; i<clause_lit_count[c]; ++i)
            {
                clause_lit[c][i].clause_num = c;
                clause_lit[c][i].var_num = abs(temp_lit[i]);
                if (temp_lit[i] > 0) clause_lit[c][i].sense = 1;
                else clause_lit[c][i].sense = 0;

                var_lit_count[clause_lit[c][i].var_num]++;
            }
            clause_lit[c][i].var_num=0;
            clause_lit[c][i].clause_num = -1;

            //unit clause
            if(clause_lit_count[c]==1)
            {
                unitclause_queue[unitclause_queue_end_pointer++] = clause_lit[c][0];
                clause_delete[c]=1;
            }

            if(clause_lit_count[c] > max_clause_len)
                max_clause_len = clause_lit_count[c];
            else if(clause_lit_count[c] < min_clause_len)
                min_clause_len = clause_lit_count[c];

            formula_len += clause_lit_count[c];
        }
        infile.close();

        avg_clause_len = (double)formula_len/num_clauses;

        if(unitclause_queue_end_pointer>0)
        {
            simplify = 1;
            for (c = 0; c < num_clauses; c++)
            {
                org_clause_lit_count[c] = clause_lit_count[c];
                org_clause_lit[c] = new lit[clause_lit_count[c]+1];
                for(i=0; i<org_clause_lit_count[c]; ++i)
                {
                    org_clause_lit[c][i] = clause_lit[c][i];
                }

            }
        }


        //creat var literal arrays
        for (v=1; v<=num_vars; ++v)
        {
            var_lit[v] = new lit[var_lit_count[v]+1];
            var_lit_count[v] = 0;	//reset to 0, for build up the array
        }
        //scan all clauses to build up var literal arrays
        for (c = 0; c < num_clauses; ++c)
        {
            for(i=0; i<clause_lit_count[c]; ++i)
            {
                v = clause_lit[c][i].var_num;
                var_lit[v][var_lit_count[v]] = clause_lit[c][i];
                ++var_lit_count[v];
            }
        }
        for (v=1; v<=num_vars; ++v) //set boundary
            var_lit[v][var_lit_count[v]].clause_num=-1;

        return 1;
    }


    void build_neighbor_relation()
    {
        int*	neighbor_flag = new int[num_vars+1];
        int		i,j,count;
        int 	v,c;

        for(v=1; v<=num_vars; ++v)
        {
            var_neighbor_count[v] = 0;

            if(fix[v]==1) continue;

            for(i=1; i<=num_vars; ++i)
                neighbor_flag[i] = 0;
            neighbor_flag[v] = 1;

            for(i=0; i<var_lit_count[v]; ++i)
            {
                c = var_lit[v][i].clause_num;
                if(clause_delete[c]==1) continue;

                for(j=0; j<clause_lit_count[c]; ++j)
                {
                    if(neighbor_flag[clause_lit[c][j].var_num]==0)
                    {
                        var_neighbor_count[v]++;
                        neighbor_flag[clause_lit[c][j].var_num] = 1;
                    }
                }
            }

            neighbor_flag[v] = 0;

            var_neighbor[v] = new int[var_neighbor_count[v]+1];

            count = 0;
            for(i=1; i<=num_vars; ++i)
            {
                if(fix[i]==1) continue;

                if(neighbor_flag[i]==1)
                {
                    var_neighbor[v][count] = i;
                    count++;
                }
            }
            var_neighbor[v][count]=0;
        }

        delete[] neighbor_flag;
        neighbor_flag=NULL;
    }


    void print_solution()
    {
        int    i;

        cout<<"v ";
        for (i=1; i<=num_vars; i++) {
            if(cur_soln[i]==0) cout<<"-";
            cout<<i;
            if(i%10==0) cout<<endl<<"v ";
            else	cout<<' ';
        }
        cout<<"0"<<endl;
    }


    int verify_sol()
    {
        int c,j;
        int flag;

        if(simplify==0)
        {

            for (c = 0; c<num_clauses; ++c)
            {
                flag = 0;
                for(j=0; j<clause_lit_count[c]; ++j)
                    if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {
                        flag = 1;
                        break;
                    }

                if(flag ==0) { //output the clause unsatisfied by the solution
                    cout<<"c clause "<<c<<" is not satisfied"<<endl;

                    cout<<"c ";
                    for(j=0; j<clause_lit_count[c]; ++j)
                    {
                        if(clause_lit[c][j].sense==0)cout<<"-";
                        cout<<clause_lit[c][j].var_num<<" ";
                    }
                    cout<<endl;

                    for(j=0; j<clause_lit_count[c]; ++j)
                        cout<<cur_soln[clause_lit[c][j].var_num]<<" ";
                    cout<<endl;

                    return 0;
                }
            }
        }

        if(simplify==1)
        {
            for (c = 0; c<num_clauses; ++c)
            {
                flag = 0;
                for(j=0; j<org_clause_lit_count[c]; ++j)
                    if (cur_soln[org_clause_lit[c][j].var_num] == org_clause_lit[c][j].sense) {
                        flag = 1;
                        break;
                    }

                if(flag ==0) { //output the clause unsatisfied by the solution
                    cout<<"c clause "<<c<<" is not satisfied"<<endl;

                    if(clause_delete[c]==1)cout<<"c this clause is deleted by UP."<<endl;

                    cout<<"c ";
                    for(j=0; j<org_clause_lit_count[c]; ++j)
                    {
                        if(org_clause_lit[c][j].sense==0)cout<<"-";
                        cout<<org_clause_lit[c][j].var_num<<" ";
                    }
                    cout<<endl;

                    for(j=0; j<org_clause_lit_count[c]; ++j)
                        cout<<cur_soln[org_clause_lit[c][j].var_num]<<" ";
                    cout<<endl;

                    return 0;
                }
            }

        }

        return 1;
    }

// static
    int pick_var(void)
    {
        int         i,k,c,v;
        int         best_var;
        lit*		clause_c;

        /**Greedy Mode**/
        /*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
        if(goodvar_stack_fill_pointer>0)
        {

            //if(goodvar_stack_fill_pointer<balancePar)
            //{
            best_var = goodvar_stack[0];
            for(i=1; i<goodvar_stack_fill_pointer; ++i)
            {
                v=goodvar_stack[i];
                if(score[v]>score[best_var]) best_var = v;
                else if(score[v]==score[best_var])
                {
                    //if(unsat_app_count[v]>unsat_app_count[best_var]) best_var = v;
                    //else if(unsat_app_count[v]==unsat_app_count[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;

                    if(time_stamp[v]<time_stamp[best_var]) best_var = v;
                }
            }
            return best_var;
            //}
            /*else
            {
            	best_var = goodvar_stack[rand()%goodvar_stack_fill_pointer];
            	for(int j=1;j<balancePar;++j)
            	{
            		v = goodvar_stack[rand()%goodvar_stack_fill_pointer];
            		if(score[v]>score[best_var]) best_var = v;
            		else if(score[v]==score[best_var])
            		{
            			//if(unsat_app_count[v]>unsat_app_count[best_var]) best_var = v;
            			//else if(unsat_app_count[v]==unsat_app_count[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
            			if(time_stamp[v]<time_stamp[best_var]) best_var = v;
            		}
            	}
            	return best_var;
            }*/
        }


        /*aspiration*/
        if (aspiration_active)
        {
            best_var = 0;
            for(i=0; i<unsatvar_stack_fill_pointer; ++i)
            {
                if(score[unsatvar_stack[i]]>ave_weight)
                {
                    best_var = unsatvar_stack[i];
                    break;
                }
            }

            for(++i; i<unsatvar_stack_fill_pointer; ++i)
            {
                v=unsatvar_stack[i];
                if(score[v]>score[best_var]) best_var = v;
                else if(score[v]==score[best_var] && time_stamp[v]<time_stamp[best_var]) best_var = v;
            }

            if(best_var!=0) return best_var;
        }
        /*****end aspiration*******************/

        update_clause_weights();

        /*focused random walk*/

        c = unsat_stack[rand()%unsat_stack_fill_pointer];
        clause_c = clause_lit[c];
        best_var = clause_c[0].var_num;
        for(k=1; k<clause_lit_count[c]; ++k)
        {
            v=clause_c[k].var_num;

            //using score
            //if(score[v]>score[best_var]) best_var = v;
            //else if(score[v]==score[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;

            //using unweighted make
            if(unsat_app_count[v]>unsat_app_count[best_var]) best_var = v;
            //else if(unsat_app_count[v]==unsat_app_count[best_var] && time_stamp[v]<time_stamp[best_var]) best_var = v;
            else if(unsat_app_count[v]==unsat_app_count[best_var])
            {
                if(score[v]>score[best_var]) best_var = v;
                else if(score[v]==score[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
            }
        }

        return best_var;
    }




//set functions in the algorithm
    void settings()
    {
        //set_clause_weighting();

        //aspiration_active = false; //
    }

    /*
    void local_search(int max_flips)
    {
    	int flipvar;

    	for (step = 0; step<max_flips; step++)
    	{
    		//find a solution
    		if(unsat_stack_fill_pointer==0) return;

    		flipvar = pick_var();

    		flip(flipvar);

    		time_stamp[flipvar] = step;
    	}
    }
    */
//void flip(int flipvar);

    void local_search(long long no_improv_times)
    {
        int flipvar;
        long long notime = 1 + no_improv_times;

        while(--notime)
        {
            step++;

            flipvar = pick_var();
            flip(flipvar);
            time_stamp[flipvar] = step;

            if(unsat_stack_fill_pointer < this_try_best_unsat_stack_fill_pointer)
            {
                this_try_best_unsat_stack_fill_pointer = unsat_stack_fill_pointer;
                notime = 1 + no_improv_times;
            }

            if(unsat_stack_fill_pointer == 0)
            {
                return;
            }
        }

        return;
    }

    void default_settings()
    {
        seed = 1;
        ls_no_improv_times = 200000;
        p_scale = 0.3;
        q_scale = 0.7;
        threshold = 50;

        aspiration_active = false; //
    }

    bool parse_arguments(int argc, char ** argv)
    {

        bool flag_inst = false;
        default_settings();
        cout << "You have entered " << argc
             << " arguments:" << "\n";

        for (int i = 0; i < argc; ++i)
            cout << argv[i] << "\n";

        for (int i=1; i<argc; i++)
        {
            if(strcmp(argv[i],"-inst")==0)
            {
                i++;
                if(i>=argc) return false;
                inst = argv[i];
                flag_inst = true;
                continue;
            }
            else if(strcmp(argv[i],"-seed")==0)
            {
                i++;
                if(i>=argc) return false;
                sscanf(argv[i], "%d", &seed);
                continue;
            }

            else if(strcmp(argv[i],"-aspiration")==0)
            {
                i++;
                if(i>=argc) return false;
                int tmp;
                sscanf(argv[i], "%d", &tmp);
                if (tmp==1)
                    aspiration_active = true;
                else 	aspiration_active = false;
                continue;
            }

            else if(strcmp(argv[i],"-swt_threshold")==0)
            {
                i++;
                if(i>=argc) return false;
                sscanf(argv[i], "%d", &threshold);
                continue;
            }
            else if(strcmp(argv[i],"-swt_p")==0)
            {
                i++;
                if(i>=argc) return false;
                sscanf(argv[i], "%f", &p_scale);
                continue;
            }
            else if(strcmp(argv[i],"-swt_q")==0)
            {
                i++;
                if(i>=argc) return false;
                sscanf(argv[i], "%f", &q_scale);
                continue;
            }

            else if(strcmp(argv[i],"-ls_no_improv_steps")==0) {
                i++;
                if(i>=argc) return false;
                sscanf(argv[i], "%lld", &ls_no_improv_times);
                continue;
            }
            else return false;

        }

        if (flag_inst) return true;
        else return false;

    }

    /*
    int main(int argc, char* argv[])
    {
    	int     seed,i;
    	int		satisfy_flag=0;
    	struct 	tms start, stop;

        cout<<"c This is CCAnr 2.0 [Version: 2018.01.28] [Author: Shaowei Cai]."<<endl;

    	times(&start);

    	bool ret = parse_arguments(argc, argv);
    	if(!ret) {cout<<"Arguments Error!"<<endl; return -1;}

    	//if (build_instance(argv[1])==0)
    	if(build_instance(inst) == 0)
    	{
    		cout<<"Invalid filename: "<< inst <<endl;
    		return -1;
    	}

        //sscanf(argv[2],"%d",&seed);

        srand(seed);

        if(unitclause_queue_end_pointer>0) preprocess();

        build_neighbor_relation();

        scale_ave=(threshold+1)*q_scale; //

    	cout<<"c Instance: Number of variables = "<<num_vars<<endl;
    	cout<<"c Instance: Number of clauses = "<<num_clauses<<endl;
    	cout<<"c Instance: Ratio = "<<ratio<<endl;
    	cout<<"c Instance: Formula length = "<<formula_len<<endl;
    	cout<<"c Instance: Avg (Min,Max) clause length = "<<avg_clause_len<<" ("<<min_clause_len<<","<<max_clause_len<<")"<<endl;
    	cout<<"c Algorithmic: Random seed = "<<seed<<endl;
    	cout<<"c Algorithmic: ls_no_improv_steps = " << ls_no_improv_times << endl;
    	cout<<"c Algorithmic: swt_p = " << p_scale << endl;
    	cout<<"c Algorithmic: swt_q = " << q_scale << endl;
    	cout<<"c Algorithmic: swt_threshold = " << threshold << endl;
    	cout<<"c Algorithmic: scale_ave = " << scale_ave << endl;
    	if(aspiration_active) cout<<"c Algorithmic: aspiration_active = true" << endl;
    	else cout<<"c Algorithmic: aspiration_active = false" << endl;

    	for (tries = 0; tries <= max_tries; tries++)
    	{
    		 settings();

    		 init();

    		 local_search(ls_no_improv_times);

    		 if (unsat_stack_fill_pointer==0)
    		 {
    		 	if(verify_sol()==1) {satisfy_flag = 1; break;}
    		    else cout<<"c Sorry, something is wrong."<<endl;/////
    		 }
    	}

    	times(&stop);
    	double comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

        if(satisfy_flag==1)
        {
        	cout<<"s SATISFIABLE"<<endl;
    		print_solution();
        }
        else  cout<<"s UNKNOWN"<<endl;

        cout<<"c solveSteps = "<<tries<<" tries + "<<step<<" steps (each try has "<<max_flips<<" steps)."<<endl;
        cout<<"c solveTime = "<<comp_time<<endl;

        free_memory();

        return 0;
    }
    */

    inline void unsat(int clause)
    {
        index_in_unsat_stack[clause] = unsat_stack_fill_pointer;
        push_s(clause,unsat_stack);

        //update appreance count of each var in unsat clause and update stack of vars in unsat clauses
        int v;
        for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
        {
            unsat_app_count[v]++;
            if(unsat_app_count[v]==1)
            {
                index_in_unsatvar_stack[v] = unsatvar_stack_fill_pointer;
                push_s(v,unsatvar_stack);
            }
        }
    }


    inline void sat(int clause)
    {
        int index,last_unsat_clause;

        //since the clause is satisfied, its position can be reused to store the last_unsat_clause
        last_unsat_clause = pop_s(unsat_stack);
        index = index_in_unsat_stack[clause];
        unsat_stack[index] = last_unsat_clause;
        index_in_unsat_stack[last_unsat_clause] = index;

        //update appreance count of each var in unsat clause and update stack of vars in unsat clauses
        int v,last_unsat_var;
        for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
        {
            unsat_app_count[v]--;
            if(unsat_app_count[v]==0)
            {
                last_unsat_var = pop_s(unsatvar_stack);
                index = index_in_unsatvar_stack[v];
                unsatvar_stack[index] = last_unsat_var;
                index_in_unsatvar_stack[last_unsat_var] = index;
            }
        }
    }


//initiation of the algorithm
    void init(int * soln)
    {
        int 		v,c;
        int			i,j;
        int			clause;

        //Initialize edge weights
        for (c = 0; c<num_clauses; c++)
            clause_weight[c] = 1;

        //init unsat_stack
        unsat_stack_fill_pointer = 0;
        unsatvar_stack_fill_pointer = 0;

        //init solution
        for (v = 1; v <= num_vars; v++) {

            if(fix[v]==0) {

                cur_soln[v] = soln[v];

                time_stamp[v] = 0;
                conf_change[v] = 1;
                unsat_app_count[v] = 0;

                //pscore[v] = 0;
            }

        }

        /* figure out sat_count, and init unsat_stack */
        for (c=0; c<num_clauses; ++c)
        {
            if(clause_delete[c]==1) continue;

            sat_count[c] = 0;

            for(j=0; j<clause_lit_count[c]; ++j)
            {
                if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
                {
                    sat_count[c]++;
                    sat_var[c] = clause_lit[c][j].var_num;
                }
            }

            if (sat_count[c] == 0)
                unsat(c);
        }

        /*figure out var score*/
        int lit_count;
        for (v=1; v<=num_vars; v++)
        {
            if(fix[v]==1)
            {
                score[v] = -100000;
                continue;
            }

            score[v] = 0;

            lit_count = var_lit_count[v];

            for(i=0; i<lit_count; ++i)
            {
                c = var_lit[v][i].clause_num;
                if (sat_count[c]==0) score[v]++;
                else if (sat_count[c]==1 && var_lit[v][i].sense==cur_soln[v]) score[v]--;
            }
        }

        /*
        int flag;
        //compute pscore and record sat_var and sat_var2 for 2sat clauses
        for (c=0; c<num_clauses; ++c)
        {
        	if(clause_delete[c]==1) continue;

        	if (sat_count[c]==1)
        	{
        		for(j=0;j<clause_lit_count[c];++j)
        		{
        			v=clause_lit[c][j].var_num;
        			if(v!=sat_var[c])pscore[v]++;
        		}
        	}
        	else if(sat_count[c]==2)
        	{
        		flag=0;
        		for(j=0;j<clause_lit_count[c];++j)
        		{
        			v=clause_lit[c][j].var_num;
        			if(clause_lit[c][j].sense == cur_soln[v])
        			{
        				pscore[v]--;
        				if(flag==0){sat_var[c] = v; flag=1;}
        				else	{sat_var2[c] = v; break;}
        			}
        		}

        	}
        }
        */


        //init goodvars stack
        goodvar_stack_fill_pointer = 0;
        for (v=1; v<=num_vars; v++)
        {
            if(fix[v]==1)  continue;
            if(score[v]>0)// && conf_change[v]==1)
            {
                already_in_goodvar_stack[v] = 1;
                push_s(v,goodvar_stack);

            }
            else already_in_goodvar_stack[v] = 0;
        }

        //setting for the virtual var 0
        time_stamp[0]=0;
        //pscore[0]=0;

        this_try_best_unsat_stack_fill_pointer = unsat_stack_fill_pointer;
    }

    void flip(int flipvar)
    {
        cur_soln[flipvar] = 1 - cur_soln[flipvar];

        int i,j;
        int v,c;

        lit* clause_c;

        int org_flipvar_score = score[flipvar];

        //update related clauses and neighbor vars
        for(lit *q = var_lit[flipvar]; (c=q->clause_num)>=0; q++)
        {
            clause_c = clause_lit[c];
            if(cur_soln[flipvar] == q->sense)
            {
                ++sat_count[c];

                if (sat_count[c] == 2) //sat_count from 1 to 2
                    score[sat_var[c]] += clause_weight[c];
                else if (sat_count[c] == 1) // sat_count from 0 to 1
                {
                    sat_var[c] = flipvar;//record the only true lit's var
                    for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] -= clause_weight[c];

                    sat(c);
                }
            }
            else // cur_soln[flipvar] != cur_lit.sense
            {
                --sat_count[c];
                if (sat_count[c] == 1) //sat_count from 2 to 1
                {
                    for(lit* p=clause_c; (v=p->var_num)!=0; p++)
                    {
                        if(p->sense == cur_soln[v] )
                        {
                            score[v] -= clause_weight[c];
                            sat_var[c] = v;
                            break;
                        }
                    }
                }
                else if (sat_count[c] == 0) //sat_count from 1 to 0
                {
                    for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] += clause_weight[c];
                    unsat(c);
                }//end else if

            }//end else
        }

        score[flipvar] = -org_flipvar_score;

        /*update CCD */
        int index;

        conf_change[flipvar] = 0;
        //remove the vars no longer goodvar in goodvar stack
        for(index=goodvar_stack_fill_pointer-1; index>=0; index--)
        {
            v = goodvar_stack[index];
            if(score[v]<=0)
            {
                goodvar_stack[index] = pop_s(goodvar_stack);
                already_in_goodvar_stack[v] = 0;
            }
        }

        //update all flipvar's neighbor's conf_change to be 1, add goodvar
        int* p;
        for(p=var_neighbor[flipvar]; (v=*p)!=0; p++)
        {
            conf_change[v] = 1;

            if(score[v]>0 && already_in_goodvar_stack[v] ==0)
            {
                push_s(v,goodvar_stack);
                already_in_goodvar_stack[v] = 1;
            }
        }
    }


    int run(int * soln, int seedp)
    {


        int     seed = seedp;
        int		satisfy_flag=0;
        struct 	tms start, stop;
        using std::cout, std::endl;

        if(verbosity>1)std::cout<<"c This is CCAnr 2.0 [Version: 2018.01.28] [Author: Shaowei Cai]."<<std::endl;
        times(&start);

        srand(seed);

        //if(unitclause_queue_end_pointer>0) preprocess();  //Arijit : preprocess is stopped.


        scale_ave=(threshold+1)*q_scale; //
        if(verbosity>1) {
            cout<<"c Instance: Number of variables = "<<num_vars<<endl;
            cout<<"c Instance: Number of clauses = "<<num_clauses<<endl;
            cout<<"c Instance: Ratio = "<<ratio<<endl;
            cout<<"c Instance: Formula length = "<<formula_len<<endl;
            cout<<"c Instance: Avg (Min,Max) clause length = "<<avg_clause_len<<" ("<<min_clause_len<<","<<max_clause_len<<")"<<endl;
            cout<<"c Algorithmic: Random seed = "<<seed<<endl;
            cout<<"c Algorithmic: ls_no_improv_steps = " << ls_no_improv_times << endl;
            cout<<"c Algorithmic: swt_p = " << p_scale << endl;
            cout<<"c Algorithmic: swt_q = " << q_scale << endl;
            cout<<"c Algorithmic: swt_threshold = " << threshold << endl;
            cout<<"c Algorithmic: scale_ave = " << scale_ave << endl;
            if(aspiration_active) cout<<"c Algorithmic: aspiration_active = true" << endl;
            else cout<<"c Algorithmic: aspiration_active = false" << endl;
        }
        for (tries = 0; tries <= max_tries; tries++)
        {
            settings();

            init(soln);

            local_search(ls_no_improv_times);

            if (unsat_stack_fill_pointer==0)
            {
                if(verify_sol()==1) {
                    satisfy_flag = 1;
                    break;
                }
                else cout<<"c Sorry, something is wrong."<<endl;/////
            }
        }

        times(&stop);
        double comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

        if(satisfy_flag==1)
        {
            if(verbosity>0)cout<<"c [CCAnr]SATISFIABLE"<<endl;
            if(verbosity>1)print_solution();
        }
        else  if(verbosity>0)cout<<"c [CCAnr] UNKNOWN"<<endl;
        if(verbosity>1) {
            cout<<"c solveSteps = "<<tries<<" tries + "<<step<<" steps (each try has "<<max_flips<<" steps)."<<endl;
            cout<<"c solveTime = "<<comp_time<<endl;
        }

//     free_memory();

        return 0;
    }
    void unit_propagation()
    {
        lit uc_lit;
        int uc_clause;
        int uc_var;
        bool uc_sense;

        int c,v;
        int i,j;
        lit cur, cur_c;


        //while (unitclause_queue_beg_pointer < unitclause_queue_end_pointer)
        for(unitclause_queue_beg_pointer=0; unitclause_queue_beg_pointer < unitclause_queue_end_pointer; unitclause_queue_beg_pointer++)
        {
            uc_lit = unitclause_queue[unitclause_queue_beg_pointer];

            uc_var = uc_lit.var_num;
            uc_sense = uc_lit.sense;

            if(fix[uc_var]==1) {
                if(uc_sense!=cur_soln[uc_var])cout<<"c wants to fix a variable twice, forbid."<<endl;
                continue;
            }

            cur_soln[uc_var] = uc_sense;//fix the variable in unit clause
            fix[uc_var] = 1;

            for(i = 0; i<var_lit_count[uc_var]; ++i)
            {
                cur = var_lit[uc_var][i];
                c = cur.clause_num;

                if(clause_delete[c]==1) continue;

                if(cur.sense == uc_sense)//then remove the clause from var's var_lit[] array
                {
                    clause_delete[c]=1;
                }
                else
                {
                    if(clause_lit_count[c]==2)
                    {
                        if(clause_lit[c][0].var_num == uc_var)
                        {
                            unitclause_queue[unitclause_queue_end_pointer++] = clause_lit[c][1];
                        }
                        else
                        {
                            unitclause_queue[unitclause_queue_end_pointer++] = clause_lit[c][0];
                        }

                        clause_delete[c]=1;
                    }
                    else
                    {
                        for(j=0; j<clause_lit_count[c]; ++j)
                        {
                            if(clause_lit[c][j].var_num == uc_var)
                            {
                                clause_lit[c][j]=clause_lit[c][clause_lit_count[c]-1];

                                clause_lit_count[c]--;

                                break;
                            }
                        }//for
                    }
                }

            }//for



        }//begpointer to endpointer for

    }


    void preprocess()
    {
        int c,v,i;
        int delete_clause_count=0;
        int fix_var_count=0;

        unit_propagation();

        //rescan all clauses to build up var literal arrays
        for (v=1; v<=num_vars; ++v)
            var_lit_count[v] = 0;

        max_clause_len = 0;
        min_clause_len = num_vars;
        int    formula_len=0;

        for (c = 0; c < num_clauses; ++c)
        {
            if(clause_delete[c]==1) {
                delete_clause_count++;
                continue;
            }

            for(i=0; i<clause_lit_count[c]; ++i)
            {
                v = clause_lit[c][i].var_num;
                var_lit[v][var_lit_count[v]] = clause_lit[c][i];
                ++var_lit_count[v];
            }
            clause_lit[c][i].var_num=0; //new clause boundary
            clause_lit[c][i].clause_num = -1;

            //about clause length
            formula_len += clause_lit_count[c];

            if(clause_lit_count[c] > max_clause_len)
                max_clause_len = clause_lit_count[c];
            else if(clause_lit_count[c] < min_clause_len)
                min_clause_len = clause_lit_count[c];
        }

        avg_clause_len = (double)formula_len/num_clauses;

        for (v=1; v<=num_vars; ++v)
        {
            if(fix[v]==1)
            {
                fix_var_count++;
            }
            var_lit[v][var_lit_count[v]].clause_num=-1;//new var_lit boundary
        }

//     cout<<"c unit propagation fixes "<<fix_var_count<<" variables, and delets "<<delete_clause_count<<" clauses"<<endl;

    }

    int		ave_weight=1;
    int		delta_total_weight=0;

    /**************************************** clause weighting for 3sat **************************************************/

    int		threshold;
    float	p_scale;//w=w*p+ave_w*q
    float	q_scale=0;
    int		scale_ave;//scale_ave==ave_weight*q_scale

    int 	q_init=0;

    void smooth_clause_weights()
    {
        int i,j,c,v;
        int new_total_weight=0;

        for (v=1; v<=num_vars; ++v)
            score[v] = 0;

        //smooth clause score and update score of variables
        for (c = 0; c<num_clauses; ++c)
        {
            clause_weight[c] = clause_weight[c]*p_scale+scale_ave;
            if(clause_weight[c]<1) clause_weight[c] = 1;

            new_total_weight+=clause_weight[c];

            //update score of variables in this clause
            if (sat_count[c]==0)
            {
                for(j=0; j<clause_lit_count[c]; ++j)
                {
                    score[clause_lit[c][j].var_num] += clause_weight[c];
                }
            }
            else  if(sat_count[c]==1)
                score[sat_var[c]]-=clause_weight[c];
        }

        ave_weight=new_total_weight/num_clauses;
    }

    void update_clause_weights()
    {
        int i,v;

        for(i=0; i < unsat_stack_fill_pointer; ++i)
            clause_weight[unsat_stack[i]]++;

        for(i=0; i<unsatvar_stack_fill_pointer; ++i)
        {
            v = unsatvar_stack[i];
            score[v] += unsat_app_count[v];
            if(score[v]>0 &&  conf_change[v]==1 && already_in_goodvar_stack[v] ==0)
            {
                push_s(v,goodvar_stack);
                already_in_goodvar_stack[v] =1;
            }
        }

        delta_total_weight+=unsat_stack_fill_pointer;
        if(delta_total_weight>=num_clauses)
        {
            ave_weight+=1;
            delta_total_weight -= num_clauses;

            //smooth weights
            if(ave_weight>threshold)
                smooth_clause_weights();
        }
    }


    void set_clause_weighting()
    {
        threshold=300;
        p_scale=0.3;
        if(q_init==0)
        {
            if(ratio<=15) q_scale=0;
            else q_scale=0.7;
        }
        else
        {
            if(q_scale<0.5)  //0
                q_scale = 0.7;
            else
                q_scale = 0;
        }

        scale_ave=(threshold+1)*q_scale;
        q_init = 1;
    }




}; //end class ccanr

CCAnr::~CCAnr()
{
    free_memory();
}


#endif
