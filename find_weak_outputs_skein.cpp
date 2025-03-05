// Created on: 4 Mar 2025
// Author: Oleg Zaikin
// E-mail: zaikin.icc@gmail.com
//
// Generates random regular outputs for the Skein-512 compression function,
// and runs a CDCL solver on CNFs that encode the preimage attack
// on round-reduced Skein-512 compression function.
//
// Usage : find_weak_outputs cpu-cores
//
// Example:
//     ./find_weak_outputs 12
//   runs the application on 12 CPU cores.
//=============================================================================

/*
operat_num : 3 , unsat_inst : 1 , runtime : 0.028 , cur_total_runtime : 0.028
operat_num : 4 , unsat_inst : 2 , runtime : 0.022 , cur_total_runtime : 0.05
operat_num : 5 , unsat_inst : 2 , runtime : 2.975 , cur_total_runtime : 3.025
operat_num : 6 , unsat_inst : 2 , runtime : 13.876 , cur_total_runtime : 16.901
operat_num : 7 , unsat_inst : 2 , runtime : 11.126 , cur_total_runtime : 28.027
*/

#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <random>
#include <assert.h>
#include <fstream>
#include <chrono>

#include <omp.h>

using namespace std;

string version = "0.0.2";

#define time_point_t chrono::time_point<chrono::system_clock>

enum result{ UNSAT = 0, SAT = 1, INTERR = 2 };

// 1r_3..7of12
unsigned MAX_LIMITS_SEC[5] = {3, 4, 5, 20, 30};
const unsigned MAX_UNSAT_INST = 3;
const unsigned SEQ_LEN = 512;
const unsigned SUBSEQ_LEN_1 = 8;
const unsigned SUBSEQ_LEN_2 = 16;
const string CNF_NAME_PART_1 = "cbmc_skein_1r_";
const string CNF_NAME_PART_2 = "of12_template_explicit_output";
const string SOLVER = "kissat4.0.1";

void print_version() {
	cout << "version: " << version << endl;
}

void print_usage() {
	cout << "Usage : find_weak_outputs_skein cpunum"<< endl
		 << "  cpunum : CPU cores" << endl;
}

string exec(const string cmd_str) {
	char* cmd = new char[cmd_str.size() + 1];
	for (unsigned i = 0; i < cmd_str.size(); i++)
		cmd[i] = cmd_str[i];
	cmd[cmd_str.size()] = '\0';
	FILE* pipe = popen(cmd, "r");
	delete[] cmd;
	if (!pipe) return "ERROR";
	char buffer[128];
	string result = "";
	while (!feof(pipe)) {
		if (fgets(buffer, 128, pipe) != NULL)
			result += buffer;
	}
	pclose(pipe);
	return result;
}

string rand_seq8(mt19937 &rng) {
    uniform_int_distribution<int> dist(0, 1);
    stringstream sstream8;
    do {
        string inverse_bools_str = "";
        for (unsigned i=0; i<SUBSEQ_LEN_1; i++) {
            int rand = dist(rng);
            assert(rand == 1 or rand == 0);
            sstream8 << rand;
            inverse_bools_str += (rand == 1 ? "0" : "1"); 
        }
        sstream8 << inverse_bools_str;
    } while (sstream8.str().size() < SEQ_LEN);
    assert(sstream8.str().size() == SEQ_LEN);
    return sstream8.str();
}

string gen_rand_output(mt19937 &rng) {
    string str8 = rand_seq8(rng);
    return str8;
}

result read_solver_result(const string fname) {
	result res = INTERR;
	ifstream ifile(fname, ios_base::in);
	if (!ifile.is_open()) {
		cerr << "solver result file " << fname << " wasn't opened\n";
		exit(EXIT_FAILURE);
	}
	string str;
	while (getline(ifile, str)) {
		if (str.find("s SATISFIABLE") != string::npos) {
			res = SAT;
			break;
		}
		else if (str.find("s UNSATISFIABLE") != string::npos) {
			res = UNSAT;
			break;
		}
	}
	ifile.close();
	return res;
}

string gen_rand_cnf(const string rand_output, const unsigned operat_num, const unsigned seed) {
    stringstream sstream;
    sstream << CNF_NAME_PART_1 << operat_num << CNF_NAME_PART_2 << ".cnf";
    string cnf_name = sstream.str();
    sstream.clear(); sstream.str("");
    vector<string> base_clauses;
    ifstream ifile(cnf_name, ios_base::in);
    string str;
    unsigned var_num = 0;
    while (getline(ifile, str)) {
        if (str[0] == 'c') continue;
        else if (str[0] == 'p') {
            string word;
            stringstream sstream2(str);
            sstream2 >> word; // p
            sstream2 >> word; // cnf
            sstream2 >> word; // the number of variables
            istringstream(word) >> var_num;
        }
        else {
            base_clauses.push_back(str);
        }
    }
    ifile.close();
    assert(var_num > 0);
    assert(base_clauses.size() > 0);

    sstream.clear(); sstream.str("");
    sstream << CNF_NAME_PART_1 << operat_num << CNF_NAME_PART_2 << "_hashlen512_seed" << seed << ".cnf";
    string rand_cnf_name = sstream.str();
    ofstream ofile(rand_cnf_name, ios_base::out);
    ofile << "p cnf " << var_num << " " << base_clauses.size() + rand_output.size() << endl;
    for (auto x : base_clauses) {
        ofile << x << endl;
    }
    for (unsigned i=0; i < rand_output.size(); i++) {
        if (rand_output[i] == '0') ofile << "-";
        ofile << var_num - rand_output.size() + 1 + i << " 0" << endl;
    }
    ofile.close();

    return rand_cnf_name;
}

// operat_num is the number of operations between the 1st and 2nd rounds
// operat_num is in [3..7]
result solve_cnf(const string cnf_name, const unsigned operat_num,
                 const unsigned seed, const double cur_total_runtime) 
{
    assert(operat_num >= 3 and operat_num <=7);
    // Run a solver:
    unsigned time_lim = 0;
    time_lim = MAX_LIMITS_SEC[operat_num-3];
    assert(time_lim > 0);
    stringstream sstream;
    sstream << "log_solver_seed" << seed;
    string out_fname = sstream.str();
    string system_str = SOLVER + " --time=" + to_string(time_lim) + " ./" + cnf_name + " > " + out_fname;
    exec(system_str);
    result res = read_solver_result(out_fname);
    return res;
}

double elapsed_time_sec(const time_point_t start_time) {
    const time_point_t end_time = chrono::system_clock::now();
    unsigned time_millisec = chrono::duration_cast<chrono::milliseconds>(end_time - start_time).count();
    return (double)time_millisec / (double)1000; 
}

void write_to_output(const string output_fname, const string str, bool is_first = false) {
    ofstream ofile;
    if (is_first) ofile.open(output_fname, ios_base::out);
    else ofile.open(output_fname, ios_base::app);
    ofile << str;
    ofile.close();
}

int main(int argc, char **argv) {
	vector<string> str_argv;
	for (int i=0; i < argc; ++i) str_argv.push_back(argv[i]);
	assert(str_argv.size() == argc);
	if (argc == 2 and str_argv[1] == "-h") {
		print_usage();
		exit(EXIT_SUCCESS);
	}
	if (argc == 2 and str_argv[1] == "-v") {
		print_version();
		exit(EXIT_SUCCESS);
	}
	if (argc < 2) {
		print_usage();
		exit(EXIT_FAILURE);
	}

    unsigned cpu_num = stoi(str_argv[1]);
    assert(cpu_num > 0);
    omp_set_num_threads(cpu_num);

    double min_total_solving_runtime = -1;
    #pragma omp parallel for schedule(dynamic, 1)
    for (unsigned i=0; i<cpu_num; i++) {
        unsigned checked_outputs = 0;
        mt19937 rng;
        stringstream sstream_outfname;
        sstream_outfname << "out_seed" << i;
        string output_fname = sstream_outfname.str();
        stringstream sstream;
        sstream << "cpu_num : " << cpu_num << endl;
        sstream << "seed : " << i << endl;
        sstream << "start min_total_solving_runtime : " << min_total_solving_runtime << endl;
        write_to_output(output_fname, sstream.str(), true);
        sstream.clear(); sstream.str("");
        rng.seed(i);
        for (;;) {
            checked_outputs++;
            double cur_total_runtime = 0;
            string rand_output = gen_rand_output(rng);
            unsigned unsat_inst = 0;
            bool is_break = false;
            for (unsigned operat_num=3; operat_num<=7; operat_num++) {
                // Break if already all time has been used:
                if ((min_total_solving_runtime > 0) and (cur_total_runtime >= min_total_solving_runtime)) {
                    sstream << "cur_total_runtime >= min_total_solving_runtime : " << cur_total_runtime << " >= " << min_total_solving_runtime << endl;
                    write_to_output(output_fname, sstream.str());
                    sstream.clear(); sstream.str("");
                    is_break = true;
                    break;
                }
                string cnf_name = gen_rand_cnf(rand_output, operat_num, i);
                time_point_t start_time = chrono::system_clock::now();
                result res = solve_cnf(cnf_name, operat_num, i, cur_total_runtime);
                double runtime = elapsed_time_sec(start_time);
                cur_total_runtime += runtime;
                if (res == INTERR) { 
                    is_break = true;
                    break;
                }
                else if (res == UNSAT) {
                    unsat_inst++;
                }
                if (unsat_inst > MAX_UNSAT_INST) {
                    sstream << unsat_inst << " UNSAT instances while at most " << MAX_UNSAT_INST << " are needed" << endl;
                    write_to_output(output_fname, sstream.str());
                    sstream.clear(); sstream.str("");
                    is_break = true;
                    break;
                }
                sstream << "operat_num : " << operat_num << " , unsat_inst : " 
                    << unsat_inst << " , runtime : " << runtime << " , cur_total_runtime : " << cur_total_runtime << endl;
                write_to_output(output_fname, sstream.str());
                sstream.clear(); sstream.str("");
            }
            if (checked_outputs % 10 == 0) {
                sstream << checked_outputs << " checked_outputs " << endl;
                write_to_output(output_fname, sstream.str());
                sstream.clear(); sstream.str("");
            }
            if (is_break) continue;
            if ((min_total_solving_runtime < 0) or (cur_total_runtime < min_total_solving_runtime)) {
                min_total_solving_runtime = cur_total_runtime; 
                sstream << rand_output << endl;
                sstream << "Updated min_total_solving_runtime : " << min_total_solving_runtime << endl;
                cout << sstream.str() << endl;
                sstream << "checked_outputs : " << checked_outputs << endl;
                write_to_output(output_fname, sstream.str());
                sstream.clear(); sstream.str("");
            }
        }
    }

    return 0;
}
