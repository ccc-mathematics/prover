# μ — 微型 CIC 證明助手

從零設計的小而完整的型別論證明助手:核心很小,其餘(連接詞、自然數、串列、等式)都用歸納型別在標準庫裡定義。Node.js 15 以上,無外部套件;網頁版是純前端單檔。

    mu/
    ├── src/mu.js            核心 + 歸納型別 + elaborator + 策略 + 標準庫(Node 與瀏覽器共用)
    ├── bin/cli.js           命令列
    ├── web/template.html    網頁介面;web/index.html 為建置後的單檔網頁版(直接用瀏覽器開啟)
    ├── scripts/build-web.js 把 mu.js 內嵌進網頁
    ├── examples/*.mu        範例
    └── test/test.js         測試(77 項)

## 使用

    npm run demo                         # 內建範例
    node bin/cli.js examples/tree.mu     # 檢查檔案;加 --trace 逐行顯示目標
    npm test                             # 測試
    npm run build                        # 修改後重新產生 web/index.html

## 分層

| 層 | 內容 |
|---|---|
| ① 核心 | locally nameless 的項(綁定變數、區域變數、sort、常數、應用、λ、Π、洞);宇宙階層 Prop / Type / Type 1…(Prop impredicative);β δ ι 化簡、定義等價(同時負責合一)、型別推導 |
| ② 歸納型別 | `inductive` 宣告(參數 + **索引**,即歸納族):建構子形狀與正向性檢查、欄位宇宙層級檢查;自動生成遞迴子 `I.ind`(目標 Prop,歸納法)與 `I.rec`(目標 Type,定義函數),ι 化簡(含遞迴欄位的索引)由核心處理 |
| ③ elaborator | 隱式參數 `{x : A}`、洞 `_`、一階合一、把期望型別提前傳進應用、`2 + 3` / `a = b` / 數字等記號 |
| ④ 策略 | intro exact refine apply assumption have rfl symm rw induction cases constructor left right exists exfalso norm sorry,以及 **subst injection discriminate**(索引合一) |
| ⑤ 標準庫 | False True And Or Exists Nat List 與 **Eq(歸納族)** 都是 `inductive`;Not 是 `def`;Eq.symm/trans/congr/subst(用 `cases` 證)、False.elim、Nat.add 是定理或定義 |

策略與 elaborator 都不可信:所有證明項最後一律交給核心 `infer` 重新檢查。可信範圍是核心與遞迴子生成(② 的 `doInductive`)。

## 語法速覽

    inductive List (A : Type) : Type
      | nil : List A
      | cons : A -> List A -> List A
    def f {A : Type} (x : A) : B := t       axiom c : T       check t       eval t
    theorem name (h : A) : B := by          -- 後接策略;或 := 項(項模式)
      induction n with k ih
      …

項:`fun (x : A) => t`、`forall (x : A), B`、`A -> B`、`f a b`、`_`、`(t : T)`、`Prop`、`Type`、`Type 1`。

## 用策略寫資料定義

`def f … := by` 後面接策略,證明項會成為可展開的定義。目標在 Type 時,`cases` / `induction` / `subst` / `discriminate` 自動改用 `.rec`、`Eq.rec`、`False.rec`,所以依賴型的資料函數可以直接寫:

    def Vec.head {A : Type} {n : Nat} (v : Vec A (n + 1)) : A := by
      cases v with m a t     -- nil 分支被索引合一排除
      exact a
    eval Vec.head (Vec.cons 7 (Vec.cons 8 Vec.nil))   -- 7

目標必須在 Prop 或 Type(不支援 Type 1 以上)。Eq.symm / trans / congr / subst 在 prelude 裡是可展開的 `def`,所以由 `injection` / `subst` 產生的等式證明可以被計算。

## match 模式匹配

`def` / `theorem` 的本體可以寫 `match`,內部編譯成 `cases`(非遞迴)或 `induction`(結構遞迴),再逐分支 `exact`:

    def Vec.map {A B : Type} (f : A -> B) {n : Nat} (v : Vec A n) : Vec B n :=
      match v with
      | Vec.nil => Vec.nil
      | Vec.cons a t => Vec.cons (f a) (Vec.map f t)

- 一個 scrutinee(必須是區域變數)、一層建構子 pattern;分支可寫完整名稱(`Vec.cons`)或短名稱(`cons`);隱式欄位不寫,`_` 表示不使用。
- 被索引合一排除的建構子不必寫(`Vec.head` 只寫 `cons`),寫了反而報錯「分支不可能發生」;缺少分支也會報錯。
- 遞迴呼叫必須是 `f 固定參數… 遞迴欄位`(固定參數就是前面的明確參數,按原樣傳入),且 match 的對象必須是最後一個明確參數;它會被換成 `induction` 產生的 ih。沒有終止性檢查,因為只有結構遞迴能通過。
- 沒有巢狀 pattern(`cons a (cons b t)`)、多個 scrutinee、守衛與等式引理;這些都要靠多次 `match` 或策略。

## 認證式自動化(不可信的搜尋 + 可信的核心)

`auto` 與 `tauto` 的搜尋程式完全不可信:它只決定要用哪些策略,產生出來的證明項和手寫的證明一樣,最後由 86 行的核心重新檢查。搜尋有 bug 的後果只會是失敗或被核心拒絕,不會讓錯誤的證明通過。

- **`auto`**(直覺主義):命題邏輯部分是 Dyckhoff 的 G4ip(完整、會終止)——可逆規則(intro、拆 ∧/∨/∃/False、curry、modus ponens)直接套用,只有不可逆的選擇(∨ 選邊、套用假設、`(C→D)→B` 規則)才回溯並消耗深度。一階部分:用合一變數做反向鏈結(`apply` 假設)、∃ 的見證搜尋(`Exists.intro _ _`,見證由合一得到)、Eq(`rfl`、`symm`)。一階部分是啟發式的、不完整(選擇不會跨兄弟目標回溯)。
- **`tauto`**(古典):對命題裡每個原子命題用 `Classical.em` 分成 p / ¬p,葉節點交給 `auto`(原子都定了,命題邏輯就是可判定的)。最多 7 個原子。
- **公理追蹤**:每個定理/定義都會列出它依賴的公理(沿著它用到的定理一路追,`sorry` 也算)。`auto` 的證明不依賴任何公理;`tauto` 的證明依賴 `Classical.em`,所以標示「依賴公理:Classical.em」,使用它的定理也會繼承這個標示。
- **證明項就是 certificate**:`node bin/cli.js file.mu --cert` 印出每個定理的證明項;網頁版點選定理,在「證明項(certificate)」面板看。任何外部程式只要能產生 μ 的項或策略腳本(`exact` / `refine` / `theorem … := 項`),都能用同一個核心驗證,不需要信任它。

單行寫法:`theorem t : T := by auto`。

## 限制(刻意保持小)

- 歸納族:索引不能再提到被定義的型別;遞迴欄位只支援型別正好是 `I 參數 索引` 的直接遞迴(沒有巢狀、互遞迴、函數型遞迴欄位)。
- **索引合一**:`cases h` 的索引可以是任意項(`Vec A (n + 1)`、`Fin 0`):先把索引換成新變數並加上等式前提,對每個建構子用 `injection`(同建構子 → 拆成欄位等式)、`discriminate`(不同建構子 → False)、`subst`(變數 → 代換,依賴它的假設會先收回再 intro)逐一化解。injection / discriminate 的證明項由 `I.rec` 造一個「Prop 值的編碼函數」再配合 `Eq.subst` 得到,核心不需要任何改動。限制:只支援沒有索引的資料型別(Nat、List 等)上的等式、欄位型別不依賴前面欄位;`induction` 仍要求索引是互不相同的區域變數;卡住的等式會留成假設而不報錯;沒有 HEq,所以像 `cons a v = cons b w` 的第二個欄位(型別依賴 n)不會產生等式。
- `.rec` 固定消去到 `Type`、`.ind` 固定消去到 `Prop`。Prop 的歸納型別只有「語法單元型別」(零個建構子,或一個建構子且欄位都是證明或出現在索引中:False、True、And、Eq)才有 `.rec`(大消去);Or、Exists 沒有。沒有宇宙多型與累積性(cumulativity)。
- 合一是一階的:`?m x =?= t` 這類高階情形不會自動求解,motive 由 `induction` / `rw` 自己建構。
- 沒有 proof irrelevance、η 規則、結構遞迴的終止檢查(函數必須直接寫成遞迴子)、模式匹配與 typeclass。
