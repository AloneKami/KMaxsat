/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2022, Shiwei Pan
  **************************************************************************************************/

#include "MsSolver.h"
#include <vector>

#define __BMS__     15
#define __SC_NUM__  10
#define __SV_NUM__  50

#define __H_INC__    3
#define __S_INC__    1
#define __BOUND__    1

const int sp = 10;
const int min_step = 500000;
const int max_step = 2000000;
const int MY_RAND_MAX_INT = 10000000;
const float BASIC_SCALE = 0.0000001;
const float rwprob = 0.01;

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
        if(score[i] != tmp_score[i]) printf("score wrong %d %d %d %d\n", i, score[i], tmp_score[i], tmp_model[i / 2]), flag = true;
    }
    if(flag) exit(0);
    return;
}

void MsSolver::update_weight() {
    //printf("update_weight\n");
    int cls;
    if(rand() % 1000 > sp) {
        for(int i = 0; i < hard_unsat.get_strat(); i++) {
            cls = hard_unsat[i];
            ls_hard_cls[cls].fst += __H_INC__;
            for(int j = 0; j < ls_hard_cls[cls].snd->size(); j++) {
                Lit& lit = (*ls_hard_cls[cls].snd)[j];
                score[toInt(lit)] += __H_INC__;
                var_score.update(var(lit));
            }
        }
        for(int i = 0; i < soft_unsat.get_strat(); i++) {
            cls = soft_unsat[i];
            if(ls_soft_cls[cls].fst < __BOUND__) {
                ls_soft_cls[cls].fst += __S_INC__;
                for(int j = 0; j < ls_soft_cls[cls].snd->size(); j++) {
                    Lit& lit = (*ls_soft_cls[cls].snd)[j];
                    score[toInt(lit)] += __S_INC__;
                    var_score.update(var(lit));
                }
            }
        }
    }
    else {
        assert(hard_unsat.size() == pb_n_constrs);
        assert(soft_unsat.size() == soft_cls.size());
        for(int i = hard_unsat.get_strat(); i < hard_unsat.size(); i++) {
            cls = hard_unsat[i];
            if(ls_hard_cls[cls].fst > __H_INC__) {
                ls_hard_cls[cls].fst -= __H_INC__;
                for(int j = 0; j < ls_hard_cls[cls].snd->size(); j++) {
                    Lit& lit = (*ls_hard_cls[cls].snd)[j];
                    score[toInt(lit)] -= __H_INC__;
                    var_score.update(var(lit));
                }
            }
        }
        for(int i = soft_unsat.get_strat(); i < soft_unsat.size(); i++) {
            cls = soft_unsat[i];
            if(ls_soft_cls[cls].fst > 1) {
                ls_soft_cls[cls].fst -= 1;
                for(int j = 0; j < ls_soft_cls[cls].snd->size(); j++) {
                    Lit& lit = (*ls_soft_cls[cls].snd)[j];
                    score[toInt(lit)] -= 1;
                    var_score.update(var(lit));
                }
            }
        }
    }
    return;
}

void MsSolver::flip(std::vector<int>& vars, int& unsat_clause_num) {
    for(auto u : vars) {
        if(u < 0) exit(0);
        time_stamp[u] = ls_step;
        tmp_model[u] = !tmp_model[u];
        Lit tmp_lit = mkLit(u, tmp_model[u]);
        for(auto cls : lit_hard[toInt(tmp_lit)]) {
            hard_truth_num[cls]--;
            hard_sat_var[cls] -= toInt(tmp_lit);
            assert(hard_truth_num[cls] >= 0);
            if(hard_truth_num[cls] == 0) {
                for(int i = 0; i < ls_hard_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_hard_cls[cls].snd)[i];
                    assert(sign(lit) == tmp_model[var(lit)]);
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] += ls_hard_cls[cls].fst;
                    var_score.update(var(lit));
                }
                unsat_clause_num++;
                hard_unsat.update(cls);
            }
            else if(hard_truth_num[cls] == 1) {
                assert(sign(hard_sat_var[cls]) != tmp_model[var(hard_sat_var[cls])]);
                score[hard_sat_var[cls]] += ls_hard_cls[cls].fst;
                var_score.update(var(Minisat::toLit(hard_sat_var[cls])));
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
                    var_score.update(var(lit));
                }
                soft_sat_var[cls] = toInt(lit_Undef);
                soft_unsat.update(cls);
            }
            else if(soft_truth_num[cls] == 1) {
                soft_sat_var[cls] -= toInt(tmp_lit);
                score[soft_sat_var[cls]] += ls_soft_cls[cls].fst;
                var_score.update(var(Minisat::toLit(soft_sat_var[cls])));
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
                    var_score.update(var(lit));
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
                    var_score.update(var(lit));
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

int MsSolver::select_by_BMS(int min_size) {
    int max_score = 0;
    int v = -1;
    int tmp_v, tmp_score;
    int tmp_strat = var_score.get_strat();
    min_size = min(min_size, tmp_strat);
    for(int i = 0; i < min_size; i++) {
        tmp_v = var_score[rand() % tmp_strat];
        tmp_score = get_score(tmp_v, score, tmp_model);
        assert(tmp_score > 0);
        if(tmp_score > max_score) {
            max_score = tmp_score;
            v = tmp_v;
        }
        var_score.swap(tmp_v, --tmp_strat);
    }
    if(v == -1) exit(0);
    return v;
}

void MsSolver::pick_var(std::vector<int>& vars, int& unsat_clause_num) {
    vars.clear();
    selected_var.clear();
    if(var_score.get_strat() > 0) {
        vars.push_back(select_by_BMS(__BMS__));
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
                vars.push_back(var((*ls_hard_cls[sel_c].snd)[rand() % ls_hard_cls[sel_c].snd->size()]));
            }
            else {
                while(1){
                    sel_c = soft_unsat[rand() % soft_unsat.get_strat()];
                    if(ls_soft_cls[sel_c].snd->size() > 0) break;
                }
                vars.push_back(var((*ls_soft_cls[sel_c].snd)[rand() % ls_soft_cls[sel_c].snd->size()]));
            }
            return;
        }
        if(hard_unsat.get_strat() > 0) {
            min_size = min(__SC_NUM__, hard_unsat.get_strat());
            tmp_strat = hard_unsat.get_strat();
            for(int i = 0; i < min_size; i++) {
                int r = hard_unsat[rand() % tmp_strat];
                hard_unsat.swap(r, --tmp_strat);
                tmp_v = var((*ls_hard_cls[r].snd)[rand() % ls_hard_cls[r].snd->size()]);
                if(!selected[tmp_v]) continue;
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
                tmp_v = var((*ls_soft_cls[r].snd)[rand() % ls_soft_cls[r].snd->size()]);
                if(!selected[tmp_v]) continue;
                selected_var.push_back(tmp_v);
                selected[tmp_v] = true;
            }
        }
        else return;
        for(auto u : selected_var) selected[u] = false;
        if(selected_var.size() == 1) {
            vars.push_back(selected_var[0]);
            return;
        }
        max_v = selected[0];
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
            v1 = u;
            if(var_score.get_strat() > 0) {
                tmp_v = select_by_BMS(__SV_NUM__);
                tmp_score = get_score(tmp_v, score, tmp_model);
                if(score_3 + tmp_score > 0) {
                    vars.push_back(v1);
                    vars.push_back(tmp_v);
                    //return;
                }
                else if(score_3 + tmp_score > score_2) {
                    v1 = u;
                    v2 = tmp_v;
                    score_2 = score_3 + tmp_score;
                }
            }
            flip(tmp_vec, unsat_clause_num);
        }
        //update_weight();
        if(score_1 > score_2) vars.push_back(max_v);
        else vars.push_back(v1), vars.push_back(v2);
    }
    //update_weight();
    return;    
}

void MsSolver::local_search(vec<bool>& model, Int& goalvalue) {
    printf("local_search start\n");
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
            if((sign(tmp_l) && !tmp_model[var(tmp_l)]) || (!sign(tmp_l) && tmp_model[var(tmp_l)])) {
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
        if((sign(tmp_l) && !tmp_model[var(tmp_l)]) || (!sign(tmp_l) && tmp_model[var(tmp_l)])) {
            soft_sat_var[i] += toInt(tmp_l);
            soft_truth_num[i]++;
        }
        for(int j = 1; j < ls_soft_cls[i].snd->size() - 1; j++) {
            Lit& tmp_l = (*ls_soft_cls[i].snd)[j];
            if((sign(tmp_l) && !tmp_model[var(tmp_l)]) || (!sign(tmp_l) && tmp_model[var(tmp_l)])) {
                if(soft_truth_num[i] == 0) soft_sat_var[i] = 0;
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
        if(ls_step == 466365) printf("fuck\n");
        if(unsat_clause_num == 0) {
            Int currentvalue = evalGoal(soft_cls, tmp_model, soft_unsat_clause) + fixed_goalval;
            //printf("currentvalue = %d %d\n", toint(currentvalue), toint(goalvalue));
            if(currentvalue < goalvalue) {
                printf("currentvalue = %d %d %d\n", toint(currentvalue), toint(goalvalue), ls_step);
                goalvalue = currentvalue;
                no_improve_step = 0;                   
                tmp_model.copyTo(model);
            }
            if(soft_unsat.get_strat() == 0) return;
        }
        pick_var(vars, unsat_clause_num);
        flip(vars, unsat_clause_num);
        no_improve_step++;
        ls_step++;
    }
    printf("local_search finish %g\n", cpuTime());
    return;        
}