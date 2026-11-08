# μ — 微型 CIC 證明助手

從零設計的小而完整的型別論證明助手:核心很小,其餘(連接詞、自然數、串列、等式)都用歸納型別在標準庫裡定義。Node.js 15 以上,無外部套件;網頁版是純前端單檔。

    mu/
    ├── src/mu.js            核心 + 歸納型別 + elaborator + 策略 + 標準庫(Node 與瀏覽器共用)
    ├── bin/cli.js           命令列
    ├── web/template.html    網頁介面;web/index.html 為建置後的單檔網頁版(直接用瀏覽器開啟)
    ├── scripts/build-web.js 把 mu.js 內嵌進網頁
    ├── examples/*.mu        範例
    └── test/test.js         測試(46 項)

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

## 限制(刻意保持小)

- 歸納族:索引不能再提到被定義的型別;遞迴欄位只支援型別正好是 `I 參數 索引` 的直接遞迴(沒有巢狀、互遞迴、函數型遞迴欄位)。
- **索引合一**:`cases h` 的索引可以是任意項(`Vec A (n + 1)`、`Fin 0`):先把索引換成新變數並加上等式前提,對每個建構子用 `injection`(同建構子 → 拆成欄位等式)、`discriminate`(不同建構子 → False)、`subst`(變數 → 代換,依賴它的假設會先收回再 intro)逐一化解。injection / discriminate 的證明項由 `I.rec` 造一個「Prop 值的編碼函數」再配合 `Eq.subst` 得到,核心不需要任何改動。限制:只支援沒有索引的資料型別(Nat、List 等)上的等式、欄位型別不依賴前面欄位;`induction` 仍要求索引是互不相同的區域變數;卡住的等式會留成假設而不報錯;沒有 HEq,所以像 `cons a v = cons b w` 的第二個欄位(型別依賴 n)不會產生等式。
- `.rec` 固定消去到 `Type`、`.ind` 固定消去到 `Prop`;Prop 的歸納型別(包括 `Eq`)沒有 `.rec`,所以沒有 `cast : A = B → A → B` 這類 Type 值的轉型。沒有宇宙多型與累積性(cumulativity)。
- 合一是一階的:`?m x =?= t` 這類高階情形不會自動求解,motive 由 `induction` / `rw` 自己建構。
- 沒有 proof irrelevance、η 規則、結構遞迴的終止檢查(函數必須直接寫成遞迴子)、模式匹配與 typeclass。
