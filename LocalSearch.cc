/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2022, Shiwei Pan
  **************************************************************************************************/

#include "MsSolver.h"
#include <vector>

#define __BMS__     15
#define __SC_NUM__  10
#define __SV_NUM__  50

const long min_step = 10000;
const long max_step = 100000000;
const int MY_RAND_MAX_INT = 10000000;
const float BASIC_SCALE = 0.0000001;

std::string _CutParenthesesNTail(std::string&& prettyFuncon) {
    auto pos = prettyFuncon.find('(');
    if(pos != std::string::npos) prettyFuncon.erase(prettyFuncon.begin()+pos, prettyFuncon.end());
	pos = prettyFuncon.find(' ');
	if(pos != std::string::npos) prettyFuncon.erase(prettyFuncon.begin(), prettyFuncon.begin() + pos + 1);
    return std::move(prettyFuncon);
}

void MsSolver::check_answer() {
    bool flag;
    for(unsigned int i = 0; i < ls_hard_cls.size(); i++) {
        flag = false;
        for(unsigned int j = 0; j < ls_hard_cls[i].size(); j++) {
            Lit& lit = ls_hard_cls[i][j];
            //printf("%d %d %d\n", Minisat::var(lit), Minisat::sign(lit), tmp_model[Minisat::var(lit)]);
            if((sign(lit) && !tmp_model[Minisat::var(lit)]) || (!sign(lit) && tmp_model[Minisat::var(lit)])) {
                flag = true;
                break;
            }
        }
        if(!flag) printf("check_answer failed\n"), exit(0);
    }
    return;
}

void MsSolver::check_score() {
    memset(tmp_score.data(), 0, declared_n_vars * 2 * sizeof(long long));
    bool flag = false;
    for(int i = 0; i < declared_n_vars * 2; i++) {
        if(var_assump[i] || var_assump[i ^ 1]) continue;
        for(auto cls : lit_hard[i]) {
            if(hard_truth_num[cls] == 1 && ((i & 1) == !tmp_model[i / 2])) {
                tmp_score[i] += ls_hard_weight[cls];
            }
            else if(hard_truth_num[cls] == 0) {
                tmp_score[i] += ls_hard_weight[cls];
            }
        }
        for(auto cls : lit_soft[i]) {
            if(soft_truth_num[cls] == 1 && ((i & 1) == !tmp_model[i / 2])) {
                tmp_score[i] += ls_soft_weight[cls];
            }
            else if(soft_truth_num[cls] == 0) {
                tmp_score[i] += ls_soft_weight[cls];
            }
        }
        if(score[i] != tmp_score[i]) printf("score wrong %d %lld %lld %d\n", i, score[i], tmp_score[i], tmp_model[i / 2]), flag = true;
    }
    if(flag) exit(0);
    return;
}

void MsSolver::settings() {
    rdprob = 0.01;
    rwprob = 0.1;
    smooth_probability = 0.01;
    if((total_soft_weight / ls_soft_cls.size()) > 10000) {
        h_inc = 300;
        softclause_weight_threshold = 500;
    }
    else {
        h_inc = 3;
        softclause_weight_threshold = 0;
    }
    if(declared_n_vars > 2000) {
        rdprob = 0.01;
        rwprob = 0.1;
        smooth_probability = 0.0000001;
    }
    hard_large_weight_num = 0;
    //printf("%f %f %f %lld\n", rdprob, rwprob, smooth_probability, softclause_weight_threshold);
    return;
}

void MsSolver::get_neighbour() {
    std::vector<bool> nei_flag;
    std::vector<int> tmp_nei;
    int lit, tmp_lit;
    for(int i = 0; i < declared_n_vars * 2; i++) nei_flag.push_back(false);
    for(int i = 0; i < declared_n_vars; i++) {
        tmp_nei.clear();
        nei_flag[i] = true;
        for(int j = 0; j < 2; j++) {
            lit = Minisat::toInt(Minisat::mkLit(i, j));
            for(auto cls : lit_hard[lit]) {
                for(unsigned int k = 0; k < ls_hard_cls[cls].size(); k++) {
                    tmp_lit = Minisat::var(ls_hard_cls[cls][k]);
                    if(!nei_flag[tmp_lit]) {
                        tmp_nei.push_back(tmp_lit);
                        nei_flag[tmp_lit] = true;
                    }
                }
            }
            for(auto cls : lit_soft[lit]) {
                for(unsigned int k = 0; k < ls_soft_cls[cls].size(); k++) {
                    tmp_lit = Minisat::var(ls_soft_cls[cls][k]);
                    if(!nei_flag[tmp_lit]) {
                        tmp_nei.push_back(tmp_lit);
                        nei_flag[tmp_lit] = true;
                    }
                }
            }
        }
        nei_flag[i] = false;
        for(auto nei : tmp_nei) nei_flag[nei] = false;
        var_neighbour.push_back(tmp_nei);
        //printf("%d\n", var_neighbour[i].size());
    }
    //for(int i = 0; i < pb_n_vars; i++) printf("%d\n", var_neighbour[i].size());
    return;
}

void MsSolver::update_weight() {
    int cls;
    if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability && hard_large_weight_num > 0) {
        assert(soft_unsat.size() == soft_cls.size());
        for(int i = hard_unsat.get_strat(); i < hard_unsat.size(); i++) {
            cls = hard_unsat[i];
            if(ls_hard_weight[cls] > h_inc) {
                ls_hard_weight[cls] -= h_inc;
                if(hard_truth_num[cls] == 1) score[hard_sat_var[cls]] -= h_inc, var_score.update(Minisat::var(Minisat::toLit(hard_sat_var[cls])));
            }
            if(ls_hard_weight[cls] == 1) hard_large_weight_num--;
        }
        for(int i = soft_unsat.get_strat(); i < soft_unsat.size(); i++) {
            cls = soft_unsat[i];
            if(ls_soft_weight[cls] > 1) {
                ls_soft_weight[cls] -= 1;
                if(soft_truth_num[cls] == 1) score[soft_sat_var[cls]]--, var_score.update(Minisat::var(Minisat::toLit(soft_sat_var[cls])));
            }
        }
    }
    else {
        for(int i = 0; i < hard_unsat.get_strat(); i++) {
            cls = hard_unsat[i];
            if(hard_truth_num[cls] != 0) printf("hard_unsat wrong\n"), exit(0);
            if(ls_hard_weight[cls] == 1) hard_large_weight_num++;
            ls_hard_weight[cls] += h_inc;
            for(auto lit : ls_hard_cls[cls]) {
                if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                score[Minisat::toInt(lit)] += h_inc;
                var_score.update(Minisat::var(lit));
            }
        }
        for(int i = 0; i < soft_unsat.get_strat(); i++) {
            cls = soft_unsat[i];
            if(ls_soft_weight[cls] < softclause_weight_threshold) {
                ls_soft_weight[cls]++;
                for(auto lit : ls_soft_cls[cls]) {
                    if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                    score[Minisat::toInt(lit)]++;
                    var_score.update(Minisat::var(lit));
                }
            }
        }
    }
    //check_score();
    //printf("update_weight finish\n");
    return;
}

void MsSolver::flip(std::vector<int>& vars, int& unsat_clause_num) {
    //printf("flip start\n");
    for(auto u : vars) {
        if(u < 0) {
            printf("flips wrong\n");
            for(auto j : vars) printf("%d\n", j);
            exit(0);
        }
        tmp_model[u] = !tmp_model[u];
        Lit tmp_lit = mkLit(u, tmp_model[u]);
        for(auto cls : lit_hard[toInt(tmp_lit)]) {
            if(hard_truth_num[cls] < 0) continue;
            hard_truth_num[cls]--;
            hard_sat_var[cls] -= toInt(tmp_lit);
            if(hard_truth_num[cls] == 0) {
                for(auto lit : ls_hard_cls[cls]) {
                    if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] += ls_hard_weight[cls];
                    var_score.update(Minisat::var(lit));
                }
                unsat_clause_num++;
            }
            else if(hard_truth_num[cls] == 1) {
                score[hard_sat_var[cls]] += ls_hard_weight[cls];
                var_score.update(Minisat::var(Minisat::toLit(hard_sat_var[cls])));
            }
            hard_unsat.update(cls);
        }
        for(auto cls : lit_soft[toInt(tmp_lit)]) {
            if(soft_truth_num[cls] < 0) continue;
            soft_truth_num[cls]--;
            soft_sat_var[cls] -= toInt(tmp_lit);
            if(soft_truth_num[cls] == 0) {
                for(auto lit : ls_soft_cls[cls]) {
                    if(lit == tmp_lit) continue;
                    if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                    score[toInt(lit)] += ls_soft_weight[cls];
                    var_score.update(Minisat::var(lit));
                }
            }
            else if(soft_truth_num[cls] == 1) {
                score[soft_sat_var[cls]] += ls_soft_weight[cls];
                var_score.update(Minisat::var(Minisat::toLit(soft_sat_var[cls])));
            }
            soft_unsat.update(cls);
        }
        tmp_lit = mkLit(u, !tmp_model[u]);
        for(auto cls : lit_hard[toInt(tmp_lit)]) {
            if(hard_truth_num[cls] < 0) continue;
            if(hard_truth_num[cls] == 0) {
                for(auto lit : ls_hard_cls[cls]) {
                    if(lit == tmp_lit) continue;
                    if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                    score[Minisat::toInt(lit)] -= ls_hard_weight[cls];
                    var_score.update(Minisat::var(lit));
                }
                unsat_clause_num--;
            }
            else if(hard_truth_num[cls] == 1) {
                score[hard_sat_var[cls]] -= ls_hard_weight[cls];
                var_score.update(Minisat::var(Minisat::toLit(hard_sat_var[cls])));
            }
            hard_truth_num[cls]++;
            hard_sat_var[cls] += toInt(tmp_lit);
            hard_unsat.update(cls);
        }
        for(auto cls : lit_soft[toInt(tmp_lit)]) {
            if(soft_truth_num[cls] < 0) continue;
            if(soft_truth_num[cls] == 0) {
                for(auto lit : ls_soft_cls[cls]) {
                    if(lit == tmp_lit) continue;
                    if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                    score[Minisat::toInt(lit)] -= ls_soft_weight[cls];
                    var_score.update(Minisat::var(lit));
                }
            }
            else if(soft_truth_num[cls] == 1) {
                score[soft_sat_var[cls]] -= ls_soft_weight[cls];
                var_score.update(Minisat::var(Minisat::toLit(soft_sat_var[cls])));
            }
            soft_truth_num[cls]++;
            soft_sat_var[cls] += toInt(tmp_lit);
            soft_unsat.update(cls);
        }
        var_score.update(u);
    }
    //check_score();
    return;
}

void MsSolver::pseudo_flip(int var) {
    int tt_l;
    if(var < 0) {
        printf("pseudo_flips wrong\n");
        exit(0);
    }
    var_score2.clear();
    for(auto u : var_neighbour[var]) {
        //printf("%d %d %d %d\n", u, var_score2.size(), var_neighbour[var].size(), pcnt++);
        if(var_assump[Minisat::toInt(Minisat::mkLit(u, false))] || var_assump[Minisat::toInt(Minisat::mkLit(u, true))]) continue;
        score2[Minisat::toInt(Minisat::mkLit(u, true))] = score[Minisat::toInt(Minisat::mkLit(u, true))];
        score2[Minisat::toInt(Minisat::mkLit(u, false))] = score[Minisat::toInt(Minisat::mkLit(u, false))];
        //printf("---\n");
        var_score2.insert(u);
        //printf("--\n");
    }
    Lit tmp_lit = mkLit(var, !tmp_model[var]);
    for(auto cls : lit_hard[toInt(tmp_lit)]) {
        if(hard_truth_num[cls] == 1) {
            for(auto lit : ls_hard_cls[cls]) {
                if(lit == tmp_lit) continue;
                if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                score2[toInt(lit)] += ls_hard_weight[cls];
                var_score2.update(Minisat::var(lit));
            }
        }
        else if(hard_truth_num[cls] == 2) {
            tt_l = hard_sat_var[cls] - toInt(tmp_lit);
            score2[tt_l] += ls_hard_weight[cls];
            var_score2.update(Minisat::var(Minisat::toLit(tt_l)));
        }
    }
    for(auto cls : lit_soft[toInt(tmp_lit)]) {
        if(soft_truth_num[cls] == 1) {
            for(auto lit : ls_soft_cls[cls]) {
                if(lit == tmp_lit) continue;
                if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                score2[toInt(lit)] += ls_soft_weight[cls];
                var_score2.update(Minisat::var(lit));
            }
        }
        else if(soft_truth_num[cls] == 2) {
            tt_l = soft_sat_var[cls] - toInt(tmp_lit);
            score2[tt_l] += ls_soft_weight[cls];
            var_score2.update(Minisat::var(Minisat::toLit(tt_l)));
        }
    }
    tmp_lit = mkLit(var, tmp_model[var]);
    for(auto cls : lit_hard[toInt(tmp_lit)]) {
        if(hard_truth_num[cls] == 0) {
            for(auto lit : ls_hard_cls[cls]) {
                if(lit == tmp_lit) continue;
                if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                score2[toInt(lit)] -= ls_hard_weight[cls];
                var_score2.update(Minisat::var(lit));
            }
        }
        else if(hard_truth_num[cls] == 1) {
            score2[hard_sat_var[cls]] -= ls_hard_weight[cls];
            var_score2.update(Minisat::var(Minisat::toLit(hard_sat_var[cls])));
        }
    }
    for(auto cls : lit_soft[toInt(tmp_lit)]) {
        if(soft_truth_num[cls] == 0) {
            for(auto lit : ls_soft_cls[cls]) {
                if(lit == tmp_lit) continue;
                if(var_assump[Minisat::toInt(lit)] || var_assump[Minisat::toInt(~lit)]) continue;
                score2[toInt(lit)] -= ls_soft_weight[cls];
                var_score2.update(Minisat::var(lit));
            }
        }
        else if(soft_truth_num[cls] == 1) {
            score2[soft_sat_var[cls]] -= ls_soft_weight[cls];
            var_score2.update(Minisat::var(Minisat::toLit(soft_sat_var[cls])));
        }
    }
    //printf("p finish\n");
    return;
}

int MsSolver::select_by_BMS(int min_size, int id = -1) {
    //printf("BMS s\n");
    long long max_score = 0;
    int v = -1;
    int tmp_v;
    long long tmp_score;
    int tmp_strat = var_score.get_strat();
    min_size = min(min_size, tmp_strat);
    for(int i = 0; i < min_size; i++) {
        tmp_v = var_score[rand() % tmp_strat];
        if(tmp_v == id) continue;
        tmp_score = get_score(tmp_v, score, tmp_model);
        if(tmp_score > max_score) {
            max_score = tmp_score;
            v = tmp_v;
        }
        else if(tmp_score == max_score) {
            if(time_stamp[tmp_v] < time_stamp[v]) v = tmp_v;
        }
        var_score.swap(tmp_v, --tmp_strat);
    }
    //printf("BMS f\n");
    return v;
}

int MsSolver::select_by_BMS2(int min_size, int id) {
    //printf("BMS2 s\n");
    long long max_score = 0;
    int v = -1;
    int tmp_v;
    long long tmp_score;
    int tmp_strat = var_score2.get_strat();
    min_size = min(min_size, tmp_strat);
    for(int i = 0; i < min_size; i++) {
        tmp_v = var_score2[rand() % tmp_strat];
        if(tmp_v == id) continue;
        tmp_score = get_score(tmp_v, score2, tmp_model);
        if(tmp_score > max_score) {
            max_score = tmp_score;
            v = tmp_v;
        }
        else if(tmp_score == max_score) {
            if(time_stamp[tmp_v] < time_stamp[v]) v = tmp_v;
        }
        var_score2.swap(tmp_v, --tmp_strat);
    }
    //printf("BMS2 f\n");
    return v;
}

void MsSolver::pick_var(std::vector<int>& vars) {
    //printf("pick s\n");
    vars.clear();
    selected_var.clear();
    if(var_score.get_strat() > 0) {
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob) vars.push_back(var_score[rand() % var_score.get_strat()]);
        else vars.push_back(select_by_BMS(__BMS__));
    }
    else {
        int tmp_strat, min_size, tmp_v;
        int max_v = -1;
        long long score_1 = INT_MAX;
        long long tmp_score, score_2, score_3;
        if((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob){
            update_weight();
            int sel_c;
            if(hard_unsat.get_strat() > 0) {
                sel_c = hard_unsat[rand() % hard_unsat.get_strat()];
                vars.push_back(Minisat::var(ls_hard_cls[sel_c][rand() % hard_length[sel_c]]));
            }
            else {
                if(soft_unsat.get_strat() == 0) printf("???\n");
                while(1){
                    sel_c = soft_unsat[rand() % soft_unsat.get_strat()];
                    if(soft_length[sel_c] > 0) break;
                }
                vars.push_back(Minisat::var(ls_soft_cls[sel_c][rand() % soft_length[sel_c]]));
            }
            return;
        }
        if(hard_unsat.get_strat() > 0) {
            min_size = min(__SC_NUM__, hard_unsat.get_strat());
            tmp_strat = hard_unsat.get_strat();
            for(int i = 0; i < min_size; i++) {
                int r = hard_unsat[rand() % tmp_strat];
                hard_unsat.swap(r, --tmp_strat);
                tmp_v = Minisat::var(ls_hard_cls[r][rand() % hard_length[r]]);
                if(selected[tmp_v]) continue;
                selected_var.push_back(tmp_v);
                selected[tmp_v] = true;
            }
        }
        else if(soft_unsat.get_strat() > 0) {
            min_size = min(__SC_NUM__, soft_unsat.get_strat());
            tmp_strat = soft_unsat.get_strat();
            for(int i = 0; i < min_size; i++) {
                int r = soft_unsat[rand() % tmp_strat];
                soft_unsat.swap(r, --tmp_strat);
                tmp_v = Minisat::var(ls_soft_cls[r][rand() % soft_length[r]]);
                if(selected[tmp_v]) continue;
                selected_var.push_back(tmp_v);
                selected[tmp_v] = true;
            }
        }
        else printf("????\n"), exit(0);
        for(auto u : selected_var) selected[u] = false;
        if(selected_var.size() == 1) {
            vars.push_back(selected_var[0]);
            return;
        }
        max_v = selected_var[0];
        score_1 = get_score(max_v, score, tmp_model);
        for(unsigned int i = 1; i < selected_var.size(); i++) {
            tmp_score = get_score(selected_var[i], score, tmp_model);
            if(tmp_score > score_1) {
                score_1 = tmp_score;
                max_v = tmp_v;
            }
            else if(tmp_score == score_1) {
                if(time_stamp[selected_var[i]] < time_stamp[max_v]) max_v = selected_var[i];
            }
        }
        score_2 = INT_MIN;
        std::vector<int> tmp_vec;
        int v1, v2;
        for(auto u : selected_var) {
            score_3 = get_score(u, score, tmp_model);
            tmp_vec.clear();
            tmp_vec.push_back(u); 
            //flip(tmp_vec, unsat_clause_num);
            pseudo_flip(u);
            if(var_score.get_strat() > 1) {
                //tmp_v = select_by_BMS(__SV_NUM__, u);
                //tmp_score = get_score(tmp_v, score, tmp_model);
                tmp_v = select_by_BMS2(__SV_NUM__, u);
                tmp_score = get_score(tmp_v, score2, tmp_model);
                if(score_3 + tmp_score > 0) {
                    vars.push_back(u);
                    vars.push_back(tmp_v);
                    //flip(tmp_vec, unsat_clause_num);
                    return;
                }
                else if(score_3 + tmp_score > score_2) {
                    v1 = u;
                    v2 = tmp_v;
                    score_2 = score_3 + tmp_score;
                }
                else if(score_3 + tmp_score == score_2) {
                    if(time_stamp[u] + time_stamp[tmp_v] < time_stamp[v1] + time_stamp[v2]) v1 = u, v2 = tmp_v;
                }
            }
            //flip(tmp_vec, unsat_clause_num);
        }
        update_weight();
        if(score_1 > score_2) vars.push_back(max_v);
        else vars.push_back(v1), vars.push_back(v2);
    }
    return;
}

void MsSolver::local_search(vec<bool>& best_model, Int& goalvalue, Minisat::vec<Minisat::Lit>& assump_ps) {
    int unsat_clause_num;
    int no_improve_step = 0;
    std::vector<int> vars;
    Minisat::vec<Minisat::Lit> soft_unsat_clause;
    if(ls_best_goalvalue > goalvalue) {
        best_model.copyTo(tmp_model);
        ls_step = 0;
        memset(time_stamp.data(), -1, time_stamp.size() * sizeof(int));
    }
    var_score.clear();
    hard_unsat.clear();
    soft_unsat.clear();
    for(unsigned int i = 0; i < ls_hard_cls.size(); i++) hard_truth_num[i] = 0, hard_sat_var[i] = 0;
    for(unsigned int i = 0; i < ls_soft_cls.size(); i++) soft_truth_num[i] = 0, soft_sat_var[i] = 0;
    memset(selected.data(), 0, selected.size() * sizeof(int));
    memset(score.data(), 0, score.size() * sizeof(long long));
    for(int i = 0; i < assump_ps.size(); i++) if(Minisat::var(assump_ps[i]) < declared_n_vars) var_assump[Minisat::toInt(assump_ps[i])] = 1;
    for(unsigned int i = 0; i < ls_hard_cls.size(); i++) {
        hard_length[i] = 0;
        for(unsigned int j = 0; j < ls_hard_cls[i].size(); j++) {
            Lit tmp_l = ls_hard_cls[i][j];
            if(var_assump[Minisat::toInt(tmp_l)]) {
                hard_sat_var[i] = -1;
                hard_truth_num[i] = -1;
                break;
            }
            else if(var_assump[Minisat::toInt(~tmp_l)]) continue;
            if((sign(tmp_l) && !tmp_model[Minisat::var(tmp_l)]) || (!sign(tmp_l) && tmp_model[Minisat::var(tmp_l)])) {
                hard_sat_var[i] += toInt(tmp_l);
                hard_truth_num[i]++;
            }
            std::swap(ls_hard_cls[i][j], ls_hard_cls[i][hard_length[i]++]);
        }
        if(hard_length[i] == 0) hard_sat_var[i] = -1, hard_truth_num[i] = -1;
    }
    for(unsigned int i = 0; i < ls_hard_cls.size(); i++) {
        if(hard_truth_num[i] == 1) score[hard_sat_var[i]] += ls_hard_weight[i];
        if(hard_truth_num[i] > -1) hard_unsat.insert(i);
    }
    for(unsigned int i = 0; i < ls_soft_cls.size(); i++) {
        soft_length[i] = 0;
        for(unsigned int j = 0; j < ls_soft_cls[i].size(); j++) {
            Lit tmp_l = ls_soft_cls[i][j];
            if(var_assump[Minisat::toInt(tmp_l)]) {
                soft_sat_var[i] = -1;
                soft_truth_num[i] = -1;
                break;
            }
            else if(var_assump[Minisat::toInt(~tmp_l)]) continue;
            std::swap(ls_soft_cls[i][j], ls_soft_cls[i][soft_length[i]++]);
            if((sign(tmp_l) && !tmp_model[Minisat::var(tmp_l)]) || (!sign(tmp_l) && tmp_model[Minisat::var(tmp_l)])) {
                soft_sat_var[i] += toInt(tmp_l);
                soft_truth_num[i]++;
            }
        }
        if(soft_length[i] == 0) soft_sat_var[i] = -1, soft_truth_num[i] = -1;
    }
    for(unsigned int i = 0; i < ls_soft_cls.size(); i++) {
        if(soft_truth_num[i] == 1) score[soft_sat_var[i]] += ls_soft_weight[i];
        else if(soft_truth_num[i] == 0) {
            for(unsigned int j = 0; j < ls_soft_cls[i].size(); j++) score[toInt(ls_soft_cls[i][j])] += ls_soft_weight[i];
        }
        if(soft_truth_num[i] > -1) {
            if(soft_length[i] == 0) {
                printf("%d\n", i);
                exit(0);
            }
            soft_unsat.insert(i);
        }
    }
    //for(int i = 0; i < pb_n_vars * 2; i++) if(var_assump[i] != 0) exit(0);
    for(int i = 0; i < declared_n_vars; i++) if(!var_assump[Minisat::toInt(Minisat::mkLit(i, false))] && !var_assump[Minisat::toInt(Minisat::mkLit(i, true))]) var_score.insert(i);
    unsat_clause_num = hard_unsat.get_strat();
    while(no_improve_step < min_step && ls_step < max_step && cpuTime() < opt_cpu_lim - 20) {
        //printf("%d %d %lld %lld\n", ls_step, unsat_clause_num, tolong(evalGoal(soft_cls, tmp_model, soft_unsat_clause) + fixed_goalval), tolong(goalvalue));
        if(unsat_clause_num == 0) {
            currentvalue = fixed_goalval;
            for(int i = 0; i < soft_unsat.get_strat(); i++) currentvalue += soft_cls[soft_unsat[i]].fst;
            //printf("currentvalue = %d %d %d\n", toint(currentvalue), toint(goalvalue), ls_step);
            //for(auto u : vars) printf("%d ", u);
            //printf("\n");
            if(currentvalue < best_goalvalue && currentvalue < goalvalue) {
                //reportf("\b currentvalue = %ld %ld %d %g\b\n", tolong(currentvalue), tolong(goalvalue), ls_step, cpuTime());
                //check_answer();
                local_update++;
                goalvalue = currentvalue;
                no_improve_step = 0;                   
                tmp_model.copyTo(best_model);
                ls_best_goalvalue = currentvalue;
            }
            if(soft_unsat.get_strat() == 0) return;
        }
        pick_var(vars);
        for(unsigned int i = 0; i < vars.size(); i++) time_stamp[vars[i]] = ls_step;
        flip(vars, unsat_clause_num);
        no_improve_step++;
        ls_step++;
    }
    for(int i = 0; i < assump_ps.size(); i++) if(Minisat::var(assump_ps[i]) < declared_n_vars) var_assump[Minisat::toInt(assump_ps[i])] = 0;
    for(unsigned int i = 0; i < origin_assigns.size(); i++) var_assump[origin_assigns[i]] = 1;
    return;        
}