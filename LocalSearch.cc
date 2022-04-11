/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2022, Shiwei Pan
  **************************************************************************************************/

#include "MsSolver.h"
#include <vector>

#define __BMS__     15
#define __SC_NUM__  10
#define __SV_NUM__  50

const int sp = 10;
const int min_step = 500;
const int max_step = 2000;

void MsSolver::update_weight() {
    if(rand() % 1000 < sp) {
        //for(int i = 0; i < )
    }
    else {

    }
    return;
}

void MsSolver::flip(std::vector<int>& vars, int& unsat_clause_num) {
    for(auto u : vars) {
        tmp_model[u] = !tmp_model[u];
        Lit tmp_lit = mkLit(u, !tmp_model[u]);
        printf("%d ---- %d\n", u, lit_hard[u].size());
        for(auto cls : lit_hard[u]) {
            printf("%d %d\n", cls, hard_truth_num[cls]);
            hard_truth_num[cls]--;
            if(hard_truth_num[cls] == 0) {
                for(int i = 0; i < ls_hard_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_hard_cls[cls].snd)[i];
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] += ls_hard_cls[cls].fst;
                    var_score.update(var(lit));
                }
                hard_sat_var[cls] = toInt(lit_Undef);
            }
            else if(hard_truth_num[cls] == 1) {
                printf("%d %d\n", hard_sat_var[cls], toInt(tmp_lit));
                hard_sat_var[cls] -= toInt(tmp_lit);
                printf("%d\n", hard_sat_var[cls]);
                score[hard_sat_var[cls]] += ls_hard_cls[cls].fst;
                var_score.update(var(Minisat::toLit(hard_sat_var[cls])));
            }
        }
        printf("111\n");
        for(auto cls : lit_soft[u]) {
            soft_truth_num[cls]--;
            if(soft_truth_num[cls] == 0) {
                for(int i = 0; i < ls_soft_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_soft_cls[cls].snd)[i];
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] += ls_soft_cls[cls].fst;
                    var_score.update(var(lit));
                }
                soft_sat_var[cls] = toInt(lit_Undef);
            }
            else if(soft_truth_num[cls] == 1) {
                soft_sat_var[cls] -= toInt(tmp_lit);
                score[soft_sat_var[cls]] += ls_soft_cls[cls].fst;
                var_score.update(var(Minisat::toLit(soft_sat_var[cls])));
            }
        }
        printf("222\n");
        tmp_lit = mkLit(u, tmp_model[u]);
        for(auto cls : lit_hard[u]) {
            hard_truth_num[cls]++;
            if(hard_truth_num[cls] == 1) {
                for(int i = 0; i < ls_hard_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_hard_cls[cls].snd)[i];
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] -= ls_hard_cls[cls].fst;
                    var_score.update(var(lit));
                }
                hard_sat_var[cls] = toInt(tmp_lit);
            }
            else if(hard_truth_num[cls] == 2) {
                score[hard_sat_var[cls]] -= ls_hard_cls[cls].fst;
                var_score.update(Minisat::var(Minisat::toLit(hard_sat_var[cls])));
                hard_sat_var[cls] += toInt(tmp_lit);
            }
        }
        printf("333\n");
        for(auto cls : lit_soft[u]) {
            soft_truth_num[cls]++;
            if(soft_truth_num[cls] == 1) {
                for(int i = 0; i < ls_soft_cls[cls].snd->size(); i++) {
                    Lit lit = (*ls_soft_cls[cls].snd)[i];
                    if(lit == tmp_lit) continue;
                    score[toInt(lit)] -= ls_soft_cls[cls].fst;
                    var_score.update(var(lit));
                }
                soft_sat_var[cls] = toInt(tmp_lit);
            }
            else if(soft_truth_num[cls] == 2) {
                score[soft_sat_var[cls]] -= ls_soft_cls[cls].fst;
                var_score.update(Minisat::var(Minisat::toLit(soft_sat_var[cls])));
                soft_sat_var[cls] += toInt(tmp_lit);
            }
        }
        printf("444\n");
    }
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
        tmp_score = get_score(tmp_v, score,tmp_model);
        assert(tmp_score > 0);
        if(tmp_score > max_score) {
            max_score = tmp_score;
            v = tmp_v;
        }
        var_score.swap(tmp_v, --tmp_strat);
    }
    assert(v != -1);
    return v;
}

void MsSolver::pick_var(std::vector<int>& vars) {
    printf("pick_var start\n");
    vars.clear();
    std::vector<int> FV;
    FV.clear();
    if(var_score.get_strat() > 0) {
        printf("1 %d\n", var_score.get_strat());
        vars.push_back(select_by_BMS(__BMS__));
        for(int i = 0; i < vars.size(); i++) printf("%d %d %d %d\n", vars[i], get_score(vars[i], score, tmp_model), score[toInt(mkLit(vars[i], !tmp_model[vars[i]]))], score[toInt(mkLit(vars[i], tmp_model[vars[i]]))]);
    }
    else {
        int tmp_strat, min_size, tmp_score, tmp_v;
        int max_v = -1;
        int max_score = INT_MIN;
        int score_2, score_3;
        if(hard_unsat.get_strat() > 0) {
            printf("2\n");
            min_size = min(__SC_NUM__, hard_unsat.get_strat());
            tmp_strat = hard_unsat.get_strat();
            for(int i = 0; i < min_size; i++) {
                int r = hard_unsat[rand() % tmp_strat];
                hard_unsat.swap(r, --tmp_strat);
                tmp_v = toInt((*ls_hard_cls[r].snd)[rand() % ls_hard_cls[r].snd->size()]);
                tmp_score = get_score(tmp_v, score, tmp_model);
                if(tmp_score > max_score) {
                    max_score = tmp_score;
                    max_v = tmp_v;
                }
                FV.push_back(tmp_v);
            }
        }
        else if(soft_unsat.get_strat() > 0) {
            printf("3\n");
            min_size = min(__SC_NUM__, soft_unsat.get_strat());
            tmp_strat = soft_unsat.get_strat();
            for(int i = 0; i < min_size; i++) {
                int r = soft_unsat[rand() % tmp_strat];
                soft_unsat.swap(r, --tmp_strat);
                tmp_v = toInt((*ls_soft_cls[r].snd)[rand() % ls_soft_cls[r].snd->size()]);
                tmp_score = get_score(tmp_v, score, tmp_model);
                if(tmp_score > max_score) {
                    max_score = tmp_score;
                    max_v = tmp_v;
                }
                FV.push_back(tmp_v);
            }
        }
        else return;
        score_2 = INT_MIN;
        std::vector<int> tmp_vec;
        int unsat_clause_num;
        int v1, v2;
        for(auto u : FV) {
            score_3 = get_score(var(Minisat::toLit(u)), score, tmp_model);
            tmp_vec.clear();
            tmp_vec.push_back(u); 
            flip(tmp_vec, unsat_clause_num);
            v1 = u;
            if(var_score.get_strat() > 0) {
                tmp_v = select_by_BMS(__SV_NUM__);
                tmp_score = get_score(v2, score, tmp_model);
                if(score_3 + tmp_score > 0) {
                    vars.push_back(v1);
                    vars.push_back(v2);
                    return;
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
        if(max_score > score_2) vars.push_back(max_v);
        else vars.push_back(v1), vars.push_back(v2);
    }
    printf("pick_var finish\n");
    return;    
}

void MsSolver::local_search(vec<bool>& model, Int& goalvalue) {
    Int current_value = goalvalue;
    int unsat_clause_num = 0;
    int no_improve_step = 0;
    int step = 0;
    std::vector<int> vars;
    Minisat::vec<Minisat::Lit> soft_unsat_clause;
    model.copyTo(tmp_model);
    var_score.clear();
    hard_unsat.clear();
    soft_unsat.clear();
    for(int i = 0; i < pb_n_constrs; i++) hard_truth_num[i] = 0, hard_sat_var[i] = toInt(lit_Undef);
    for(int i = 0; i < soft_cls.size(); i++) soft_truth_num[i] = 0, soft_sat_var[i] = toInt(lit_Undef);
    memset(score.data(), 0, score.size() * sizeof(int));
    bool is_satisfied;
    for(int i = 0; i < pb_n_constrs; i++) {
        for(int j = 0; j < ls_hard_cls[i].snd->size(); j++) {
            Lit tmp_l = (*ls_hard_cls[i].snd)[j];
            if((sign(tmp_l) && !tmp_model[var(tmp_l)]) || (!sign(tmp_l) && tmp_model[var(tmp_l)])) {
                if(i == 49) printf("%d ", toInt(tmp_l));
                if(hard_truth_num[i] == 0) hard_sat_var[i] = 0; 
                hard_sat_var[i] += toInt(tmp_l);
                hard_truth_num[i]++;
            }
        }
    }
    printf("\n");
    for(int i = 0; i < pb_n_constrs; i++) {
        //printf("%d %d %d\n", hard_sat_var[i], hard_clause_weight[i], score.size());
        if(hard_truth_num[i] == 1) score[hard_sat_var[i]] += ls_hard_cls[i].fst;
        hard_unsat.insert(i);
    }
    for(int i = 0; i < soft_cls.size(); i++) {
        Lit& tmp_l = *(soft_cls[i].snd)[0];
        if((sign(tmp_l) && !tmp_model[var(tmp_l)]) || (!sign(tmp_l) && tmp_model[var(tmp_l)])) {
            if(soft_truth_num[i] == 0) soft_sat_var[i] = 0;
            soft_sat_var[i] += toInt(tmp_l);
            soft_truth_num[i]++;
        }
        for(int j = 1; j < soft_cls[i].snd->size() - 1; j++) {
            Lit& tmp_l = *(soft_cls[i].snd)[j];
            if((sign(tmp_l) && !tmp_model[var(tmp_l)]) || (!sign(tmp_l) && tmp_model[var(tmp_l)])) {
                if(soft_truth_num[i] == 0) soft_sat_var[i] = 0;
                soft_sat_var[i] += toInt(tmp_l);
                soft_truth_num[i]++;
            }
        }
    }
    for(int i = 0; i < soft_cls.size(); i++) {
        soft_unsat.insert(i);
        if(soft_truth_num[i] == 1) score[soft_sat_var[i]] += ls_soft_cls[i].fst;
    }
    for(int i = 0; i < nVars(); i++) var_score.insert(i);
    while(no_improve_step < min_step && step < max_step) {
        printf("%d %d\n", no_improve_step, step);
        if(unsat_clause_num == 0) {
            Int currentvalue = evalGoal(soft_cls, tmp_model, soft_unsat_clause) + fixed_goalval;
            printf("currentvalue = %d\n", toint(currentvalue));
            if(currentvalue < goalvalue) {
                goalvalue = currentvalue;
                no_improve_step = 0;                   
                tmp_model.copyTo(model);
            }
            if(soft_unsat.get_strat() == 0) return;
        }
        pick_var(vars);
        flip(vars, unsat_clause_num);
        no_improve_step++;
        step++;
    }
    return;        
}