"use strict";
const { Univ, Var, Lam, Pi, App, Hole, subst, normalize, alphaEq, infer, pretty, fv } = require("./core");
const { parse } = require("./parser");

class ProofState {
  constructor(goalType, initialCtx = {}) {
    this.goalType = goalType;
    this.ctx = { ...initialCtx };
    this.goals = [{ id: 1, ctx: { ...initialCtx }, target: goalType }];
    this.proofTree = Hole(1);
    this.nextHoleId = 2;
  }

  instantiate(term, holeId, replacement) {
    switch (term.t) {
      case "Hole": return term.id === holeId ? replacement : term;
      case "App": return App(this.instantiate(term.fn, holeId, replacement), this.instantiate(term.arg, holeId, replacement));
      case "Lam": return Lam(term.x, term.type, this.instantiate(term.body, holeId, replacement));
      case "Pi": return Pi(term.x, term.type, this.instantiate(term.body, holeId, replacement));
      default: return term;
    }
  }

  currentGoal() {
    return this.goals[0] || null;
  }

  runTactic(line) {
    const g = this.currentGoal();
    if (!g) throw new Error("已經沒有未完成的目標!");
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith("--")) return;

    const parts = trimmed.split(/\s+/);
    const cmd = parts[0];
    const arg = trimmed.slice(cmd.length).trim();

    switch (cmd) {
      case "intro": {
        const name = arg || "h";
        const normTarget = normalize(g.target);
        if (normTarget.t !== "Pi") throw new Error("intro 失敗: 目標不是蘊含式(->)或全稱(Pi)");
        const domType = normTarget.type;
        const newTarget = subst(normTarget.body, normTarget.x, Var(name));
        const newGoal = {
          id: this.nextHoleId++,
          ctx: { ...g.ctx, [name]: domType },
          target: newTarget
        };
        const lam = Lam(name, domType, Hole(newGoal.id));
        this.proofTree = this.instantiate(this.proofTree, g.id, lam);
        this.goals.shift();
        this.goals.unshift(newGoal);
        break;
      }

      case "exact": {
        const term = parse(arg);
        const inferred = infer(term, g.ctx);
        if (!alphaEq(inferred, g.target)) {
          throw new Error("exact 失敗: 型別不符!\n得到: " + pretty(inferred) + "\n目標: " + pretty(g.target));
        }
        this.proofTree = this.instantiate(this.proofTree, g.id, term);
        this.goals.shift();
        break;
      }

      case "assumption": {
        let found = false;
        for (const [v, ty] of Object.entries(g.ctx)) {
          if (alphaEq(ty, g.target)) {
            this.proofTree = this.instantiate(this.proofTree, g.id, Var(v));
            this.goals.shift();
            found = true;
            break;
          }
        }
        if (!found) throw new Error("assumption 失敗: 沒有吻合的已知假設");
        break;
      }

case "apply": {
        const fnTerm = parse(arg);
        let fnTy = normalize(infer(fnTerm, g.ctx));
        const newSubgoals = [];
        let curApp = fnTerm;

        while (true) {
          if (alphaEq(fnTy, g.target)) break;
          if (fnTy.t !== "Pi") {
            throw new Error(`apply 失敗: ${arg} 的結論與目標不吻合\n得到: ${pretty(fnTy)}\n目標: ${pretty(g.target)}`);
          }

          // 核心關鍵：檢查是普通的 (A -> B) 還是依值量詞 (Π y:Dom, P y)
          const isDependent = fv(fnTy.body).has(fnTy.x);

          if (isDependent) {
            // 如果是全稱量詞 Π y:Dom，目標剛好是 (P x)，在已知變數中尋找能讓 body 等於 target 的項
            let matchedTerm = null;
            for (const [v] of Object.entries(g.ctx)) {
              const specialized = normalize(subst(fnTy.body, fnTy.x, Var(v)));
              if (alphaEq(specialized, g.target)) {
                matchedTerm = Var(v);
                break;
              }
            }

            if (matchedTerm) {
              curApp = App(curApp, matchedTerm);
              fnTy = normalize(subst(fnTy.body, fnTy.x, matchedTerm));
              continue;
            }
          }

          // 普通的前提子目標 (A -> B)，開闢新目標洞
          const subHoleId = this.nextHoleId++;
          newSubgoals.push({
            id: subHoleId,
            ctx: { ...g.ctx },
            target: fnTy.type
          });
          curApp = App(curApp, Hole(subHoleId));
          fnTy = normalize(subst(fnTy.body, fnTy.x, Hole(subHoleId)));
        }

        this.proofTree = this.instantiate(this.proofTree, g.id, curApp);
        this.goals.shift();
        this.goals.unshift(...newSubgoals);
        break;
      }

      case "have": {
        const m = arg.match(/^([A-Za-z_][\w']*)\s*:\s*(.+)$/);
        if (!m) throw new Error("have 格式錯誤: have 名稱 : 命題");
        const varName = m[1];
        const propTerm = parse(m[2]);
        const propTy = infer(propTerm, g.ctx);
        if (normalize(propTy).t !== "Univ") throw new Error("have 的命題必須是型別(Prop/Type)");

        const proofHole = this.nextHoleId++;
        const contHole = this.nextHoleId++;

        const goalProof = { id: proofHole, ctx: { ...g.ctx }, target: propTerm };
        const goalCont = { id: contHole, ctx: { ...g.ctx, [varName]: propTerm }, target: g.target };

        const appTerm = App(Lam(varName, propTerm, Hole(contHole)), Hole(proofHole));
        this.proofTree = this.instantiate(this.proofTree, g.id, appTerm);
        this.goals.shift();
        this.goals.unshift(goalProof, goalCont);
        break;
      }

      default:
        throw new Error("未知的策略: " + cmd);
    }
  }

  isSolved() {
    return this.goals.length === 0;
  }

  verify() {
    if (!this.isSolved()) throw new Error("仍有目標未被證明!");
    const inferred = infer(this.proofTree, this.ctx);
    if (!alphaEq(inferred, this.goalType)) throw new Error("核心檢查失敗: 證明的不是原命題!");
    return this.proofTree;
  }
}

module.exports = { ProofState };
