/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2022, Shiwei Pan
  **************************************************************************************************/

#include "MsSolver.h"
#include <vector>

#define __BMS__     15
#define __SC_NUM__  10
#define __SV_NUM__  50

const long min_step = 1000000;
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

void MsSolver::check_score() {
    memset(tmp_score.data(), 0, pb_n_vars * 2 * sizeof(long long));
    bool flag = false;
    for(int i = 0; i < pb_n_vars * 2; i++) {
        for(int j = 0; j < lit_hard[i].size(); j++) {
            int cls = lit_hard[i][j];
            if(hard_truth_num[cls] == 1 && ((i & 1) == !tmp_model[i / 2])) {
                tmp_score[i] += ls_hard_cls[cls].fst;
            }
            else if(hard_truth_num[cls] == 0) {
                tmp_score[i] += ls_hard_cls[cls].fst;
            }
        }
        for(int j = 0; j < lit_soft[i].size(); j++) {
            int cls = lit_soft[i][j];
            if(soft_truth_num[cls] == 1 && ((i & 1) == !tmp_model[i / 2])) {
                tmp_score[i] += ls_soft_cls[cls].fst;
            }
            else if(soft_truth_num[cls] == 0) {
                tmp_score[i] += ls_soft_cls[cls].fst;
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
    if(pb_n_vars > 2000) {
        rdprob = 0.01;
        rwprob = 0.1;
        smooth_probability = 0.0000001;
    }
    hard_large_weight_num = 0;
    printf("%f %f %f %lld\n", rdprob, rwprob, smooth_probability, softclause_weight_threshold);
    return;
}

void MsSolver::update_weight() {
    int cls;
    if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability && hard_large_weight_num > 0) {
        assert(soft_unsat.size() == soft_cls.size());
        for(int i = hard_unsat.get_strat(); i < hard_unsat.size(); i++) {
            cls = hard_unsat[i];
            if(ls_hard_cls[cls].fst > h_inc) {
                ls_hard_cls[cls].fst -= h_inc;
                if(hard_truth_num[cls] == 1) score[hard_sat_var[cls]] -= h_inc, var_score.update(Minisat::var(Minisat::toLit(hard_sat_var[cls])));
            }
            if(ls_hard_cls[cls].fst == 1) hard_large_weight_num--;
        }
        for(int i = soft_unsat.get_strat(); i < soft_unsat.size(); i++) {
            cls = soft_unsat[i];
            if(ls_soft_cls[cls].fst > 1) {
                ls_soft_cls[cls].fst -= 1;
                if(soft_truth_num[cls] == 1) score[soft_sat_var[cls]]--, var_score.update(Minisat::var(Minisat::toLit(soft_sat_var[cls])));
            }
        }
    }
    else {
        for(int i = 0; i < hard_unsat.get_strat(); i++) {
            cls = hard_unsat[i];
            if(ls_hard_cls[cls].fst == 1) hard_large_weight_num++;
            ls_hard_cls[cls].fst += h_inc;
            for(int j = 0; j < ls_hard_cls[cls].snd->size(); j++) {
                Lit& lit = (*ls_hard_cls[cls].snd)[j];
                score[toInt(lit)] += h_inc;
                var_score.update(Minisat::var(lit));
            }
        }
        for(int i = 0; i < soft_unsat.get_strat(); i++) {
            cls = soft_unsat[i];
            if(ls_soft_cls[cls].fst < softclause_weight_threshold) {
                ls_soft_cls[cls].fst++;
                for(int j = 0; j < ls_soft_cls[cls].snd->size(); j++) {
                    Lit& lit = (*ls_soft_cls[cls].snd)[j];
                    score[toInt(lit)]++;
                    var_score.update(Minisat::var(lit));
                }
            }
        }
    }
    return;
}

void MsSolver::flip(std::vector<int>& vars, int& unsat_clause_num) {
    for(auto u : vars) {
        if(u < 0) {
            printf("flips wrong\n");
            for(int j = 0; j < vars.size(); j++) printf("%d\n", vars[j]);
            exit(0);
        }
        tmp_model[u] = !tmp_model[u];
        Lit tmp_lit = mkLit(u, tmp_model[u]);
        for(auto cls : lit_hard[toInt(tmp_lit)]) {
            hard_truth_num[cls]--;
            hard_sat_var[cls] -= toInt(tmp_lit);
            assert(hard_truth_num[cls] >= 0);
            if(hard_truth_num[cls] == 0) {
                for(int i = 0; i < ls_hard_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_hard_cls[cls].snd)[i];
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] += ls_hard_cls[cls].fst;
                    var_score.update(Minisat::var(lit));
                }
                unsat_clause_num++;
                hard_unsat.update(cls);
            }
            else if(hard_truth_num[cls] == 1) {
                score[hard_sat_var[cls]] += ls_hard_cls[cls].fst;
                var_score.update(Minisat::var(Minisat::toLit(hard_sat_var[cls])));
            }
        }
        for(auto cls : lit_soft[toInt(tmp_lit)]) {
            soft_truth_num[cls]--;
            assert(soft_truth_num[cls] >= 0);
            if(soft_truth_num[cls] == 0) {
                for(int i = 0; i < ls_soft_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_soft_cls[cls].snd)[i];
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] += ls_soft_cls[cls].fst;
                    var_score.update(Minisat::var(lit));
                }
                soft_sat_var[cls] = toInt(lit_Undef);
                soft_unsat.update(cls);
            }
            else if(soft_truth_num[cls] == 1) {
                soft_sat_var[cls] -= toInt(tmp_lit);
                score[soft_sat_var[cls]] += ls_soft_cls[cls].fst;
                var_score.update(Minisat::var(Minisat::toLit(soft_sat_var[cls])));
            }
        }
        tmp_lit = mkLit(u, !tmp_model[u]);
        for(auto cls : lit_hard[toInt(tmp_lit)]) {
            hard_truth_num[cls]++;
            assert(hard_truth_num[cls] > 0);
            if(hard_truth_num[cls] == 1) {
                for(int i = 0; i < ls_hard_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_hard_cls[cls].snd)[i];
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] -= ls_hard_cls[cls].fst;
                    var_score.update(Minisat::var(lit));
                }
                unsat_clause_num--;
                hard_unsat.update(cls);
            }
            else if(hard_truth_num[cls] == 2) {
                score[hard_sat_var[cls]] -= ls_hard_cls[cls].fst;
                var_score.update(Minisat::var(Minisat::toLit(hard_sat_var[cls])));
            }
            hard_sat_var[cls] += toInt(tmp_lit);
        }
        for(auto cls : lit_soft[toInt(tmp_lit)]) {
            soft_truth_num[cls]++;
            assert(soft_truth_num[cls] > 0);
            if(soft_truth_num[cls] == 1) {
                for(int i = 0; i < ls_soft_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_soft_cls[cls].snd)[i];
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] -= ls_soft_cls[cls].fst;
                    var_score.update(Minisat::var(lit));
                }
                soft_unsat.update(cls);
            }
            else if(soft_truth_num[cls] == 2) {
                score[soft_sat_var[cls]] -= ls_soft_cls[cls].fst;
                var_score.update(Minisat::var(Minisat::toLit(soft_sat_var[cls])));
            }
            soft_sat_var[cls] += toInt(tmp_lit);
        }
        var_score.update(u);
    }
    //check_score();
    return;
}

int MsSolver::select_by_BMS(int min_size, int id = -1) {
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
        if(tmp_score <= 0) printf("WTF\n"), exit(0);
        if(tmp_score > max_score) {
            max_score = tmp_score;
            v = tmp_v;
        }
        else if(tmp_score == max_score) {
            if(time_stamp[tmp_v] < time_stamp[v]) v = tmp_v;
        }
        var_score.swap(tmp_v, --tmp_strat);
    }
    return v;
}

void MsSolver::pick_var(std::vector<int>& vars, int& unsat_clause_num) {
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
                vars.push_back(Minisat::var((*ls_hard_cls[sel_c].snd)[rand() % ls_hard_cls[sel_c].snd->size()]));
            }
            else {
                while(1){
                    sel_c = soft_unsat[rand() % soft_unsat.get_strat()];
                    if(ls_soft_cls[sel_c].snd->size() > 0) break;
                }
                vars.push_back(Minisat::var((*ls_soft_cls[sel_c].snd)[rand() % ls_soft_cls[sel_c].snd->size()]));
            }
            return;
        }
        if(hard_unsat.get_strat() > 0) {
            min_size = min(__SC_NUM__, hard_unsat.get_strat());
            tmp_strat = hard_unsat.get_strat();
            for(int i = 0; i < min_size; i++) {
                int r = hard_unsat[rand() % tmp_strat];
                hard_unsat.swap(r, --tmp_strat);
                tmp_v = Minisat::var((*ls_hard_cls[r].snd)[rand() % ls_hard_cls[r].snd->size()]);
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
                tmp_v = Minisat::var((*ls_soft_cls[r].snd)[rand() % ls_soft_cls[r].snd->size()]);
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
        for(int i = 1; i < selected_var.size(); i++) {
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
            flip(tmp_vec, unsat_clause_num);
            if(var_score.get_strat() > 1) {
                tmp_v = select_by_BMS(__SV_NUM__, u);
                tmp_score = get_score(tmp_v, score, tmp_model);
                if(score_3 + tmp_score > 0) {
                    vars.push_back(u);
                    vars.push_back(tmp_v);
                    flip(tmp_vec, unsat_clause_num);
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
            flip(tmp_vec, unsat_clause_num);
        }
        update_weight();
        if(score_1 > score_2) vars.push_back(max_v);
        else vars.push_back(v1), vars.push_back(v2);
    }
    //update_weight();
    return;    
}

void MsSolver::local_search(vec<bool>& model, Int& goalvalue) {
    printf("local_search start %d %g\n", toint(goalvalue), cpuTime());
    Int current_value = goalvalue;
    int unsat_clause_num = 0;
    int no_improve_step = 0;
    ls_step = 0;
    std::vector<int> vars;
    Minisat::vec<Minisat::Lit> soft_unsat_clause;
    model.copyTo(tmp_model);
    var_score.clear();
    hard_unsat.clear();
    soft_unsat.clear();
    for(int i = 0; i < pb_n_constrs; i++)       hard_truth_num[i] = 0, hard_sat_var[i] = 0;
    for(int i = 0; i < soft_cls.size(); i++)    soft_truth_num[i] = 0, soft_sat_var[i] = 0;
    memset(time_stamp.data(), -1, time_stamp.size() * sizeof(int));
    memset(selected.data(), 0, selected.size() * sizeof(int));
    memset(score.data(), 0, score.size() * sizeof(long long));
    bool is_satisfied;
    for(int i = 0; i < pb_n_constrs; i++) {
        for(int j = 0; j < ls_hard_cls[i].snd->size(); j++) {
            Lit tmp_l = (*ls_hard_cls[i].snd)[j];
            if((sign(tmp_l) && !tmp_model[Minisat::var(tmp_l)]) || (!sign(tmp_l) && tmp_model[Minisat::var(tmp_l)])) {
                hard_sat_var[i] += toInt(tmp_l);
                hard_truth_num[i]++;
            }
        }
    }
    for(int i = 0; i < pb_n_constrs; i++) {
        assert(hard_truth_num[i] > 0);
        if(hard_truth_num[i] == 1) score[hard_sat_var[i]] += ls_hard_cls[i].fst;
        hard_unsat.insert(i);
    }
    for(int i = 0; i < ls_soft_cls.size(); i++) {
        Lit& tmp_l = (*ls_soft_cls[i].snd)[0];
        if((sign(tmp_l) && !tmp_model[Minisat::var(tmp_l)]) || (!sign(tmp_l) && tmp_model[Minisat::var(tmp_l)])) {
            soft_sat_var[i] += toInt(tmp_l);
            soft_truth_num[i]++;
        }
        for(int j = 1; j < ls_soft_cls[i].snd->size() - 1; j++) {
            Lit& tmp_l = (*ls_soft_cls[i].snd)[j];
            if((sign(tmp_l) && !tmp_model[Minisat::var(tmp_l)]) || (!sign(tmp_l) && tmp_model[Minisat::var(tmp_l)])) {
                soft_sat_var[i] += toInt(tmp_l);
                soft_truth_num[i]++;
            }
        }
    }
    for(int i = 0; i < ls_soft_cls.size(); i++) {
        soft_unsat.insert(i);
        if(soft_truth_num[i] == 1) score[soft_sat_var[i]] += ls_soft_cls[i].fst;
        else if(soft_truth_num[i] == 0) {
            for(int j = 0; j < soft_cls[i].snd->size(); j++) score[toInt((*ls_soft_cls[i].snd)[j])] += ls_soft_cls[i].fst;
        }
    }
    for(int i = 0; i < pb_n_vars; i++) var_score.insert(i);
    //check_score();
    while(no_improve_step < min_step && ls_step < max_step) {
        //printf("%d %d %d %d\n", ls_step, unsat_clause_num, toint(evalGoal(soft_cls, tmp_model, soft_unsat_clause) + fixed_goalval), toint(goalvalue));
        if(unsat_clause_num == 0) {
            Int currentvalue = evalGoal(soft_cls, tmp_model, soft_unsat_clause) + fixed_goalval;
            //printf("currentvalue = %d %d %d\n", toint(currentvalue), toint(goalvalue), ls_step);
            //for(auto u : vars) printf("%d ", u);
            //printf("\n");
            if(currentvalue < goalvalue) {
                printf("currentvalue = %d %d %d %g\n", toint(currentvalue), toint(goalvalue), ls_step, cpuTime());
                goalvalue = currentvalue;
                no_improve_step = 0;                   
                tmp_model.copyTo(model);
            }
            if(soft_unsat.get_strat() == 0) return;
        }
        pick_var(vars, unsat_clause_num);
        for(int i = 0; i < vars.size(); i++) time_stamp[vars[i]] = ls_step;
        flip(vars, unsat_clause_num);
        no_improve_step++;
        ls_step++;
    }
    printf("local_search finish %g\n", cpuTime());
    return;        
}