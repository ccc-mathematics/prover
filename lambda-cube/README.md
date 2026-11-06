# λ-cube 證明助手

Barendregt λ-cube 的型別檢查器加一個小型策略層。項只有 5 種節點(變數、sort、應用、λ、Π),∧ ∨ ∃ False 都用 Π 型別(Church 編碼)定義,不寫死在核心裡。需要 Node.js 15 以上,無外部套件。

    lambda-cube/
    ├── src/cube.js          解析器、核心(infer / whnf / conv)、策略、報告(Node 與瀏覽器共用)
    ├── bin/cli.js           命令列
    ├── web/template.html    網頁介面;web/index.html 為建置後的單檔網頁版
    ├── scripts/build-web.js 內嵌 cube.js 產生網頁
    ├── examples/*.lc        範例
    └── test/test.js         測試

## 使用

    npm run demo                          # 執行內建範例
    node bin/cli.js examples/or_comm.lc   # 檢查檔案;加 --trace 逐行顯示目標
    npm test                              # 測試
    npm run build                         # 修改後重新產生 web/index.html

## 選擇 λ-cube 的頂點

腳本第一行 `system 名稱`,預設 λC。Prop 相當於 *,Type 相當於 □,Prop : Type。Π 型別的形成規則 (s1,s2) 由系統決定:

| 系統 | 額外規則 | 能做什麼 |
|---|---|---|
| λ→ | 無 | 簡單型別 |
| λ2 | Type>Prop | 多型(System F) |
| λP | Prop>Type | 依值型別 |
| λω_ | Type>Type | 型別運算子 |
| λP2 / λω / λPω_ | 以上兩兩組合 | |
| λC | 三者全有 | Calculus of Constructions |

## 腳本語法

    def f (x : A) : B := t       axiom c : T       check t       eval t
    theorem name (h : A) : B := by
      intro x / exact t / apply t / assumption / have h : T [:= t] / sorry

項:`fun (x : A) => t`、`forall (x : A), B`、`A -> B`、`f a b`(也接受 λ Π ∀ →)。`--` 開頭為註解。

## 限制

沒有歸納型別、宇宙階層、η 規則與隱式參數;`def` 不能遞迴;theorem 是不透明的(不會被展開)。化簡用「定義等價」而非最佳化,大型項會很慢。
