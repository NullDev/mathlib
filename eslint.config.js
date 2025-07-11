import tsParser from "@typescript-eslint/parser";
import tsPlugin from "@typescript-eslint/eslint-plugin";

export default [{                           // NullDev-Style ESLint Config: https://github.com/NullDevCo/JavaScript-Styleguide
    ignores: [                              // Ignore dist folders and dependencies
        "dist", "node_modules",
    ],
    files: ["**/*.js", "**/*.ts"],
    plugins: {
        "@typescript-eslint": tsPlugin,
    },
    languageOptions: {
        parser: tsParser,
        parserOptions: {
            project: "./tsconfig.json",
        },
        globals: {                          // http://eslint.org/docs/user-guide/configuring.html#specifying-environments
            browser: true,                  // browser global variables
            node: true,                     // Node.js global variables and Node.js-specific rules
            commonjs: true,                 // CommonJS global variables and CommonJS scoping
            es2022: true,                   // ESNext support
            es6: true,                      // enable all ECMAScript 6 features except for modules
        },
    },
    rules: {
        /**
         * Strict mode
         */
        strict: [2, "global"],              // http://eslint.org/docs/rules/strict
        /**
         * ES6
         */
        "no-var": 2,                        // http://eslint.org/docs/rules/no-var
        "prefer-const": 2,                  // http://eslint.org/docs/rules/prefer-const
        "prefer-destructuring": [2, {       // http://eslint.org/docs/rules/prefer-destructuring
            array: false,
            object: true,
        }, {
            enforceForRenamedProperties: false,
        }],
        /**
         * Variables
         */
        "no-shadow": 2,                     // http://eslint.org/docs/rules/no-shadow
        "no-shadow-restricted-names": 2,    // http://eslint.org/docs/rules/no-shadow-restricted-names
        "@typescript-eslint/no-unused-vars": "error",
        "no-use-before-define": 2,          // http://eslint.org/docs/rules/no-use-before-define
        /**
         * Possible errors
         */
        "comma-dangle": [                   // http://eslint.org/docs/rules/comma-dangle
            2,
            "always-multiline",
        ],
        "no-cond-assign": [2, "always"],    // http://eslint.org/docs/rules/no-cond-assign
        "no-console": 0,                    // http://eslint.org/docs/rules/no-console
        "no-debugger": 1,                   // http://eslint.org/docs/rules/no-debugger
        "no-alert": 1,                      // http://eslint.org/docs/rules/no-alert
        "no-constant-condition": 1,         // http://eslint.org/docs/rules/no-constant-condition
        "no-const-assign": 2,               // http://eslint.org/docs/rules/no-const-assign
        "no-dupe-keys": 2,                  // http://eslint.org/docs/rules/no-dupe-keys
        "no-duplicate-case": 2,             // http://eslint.org/docs/rules/no-duplicate-case
        "no-empty": 2,                      // http://eslint.org/docs/rules/no-empty
        "no-ex-assign": 2,                  // http://eslint.org/docs/rules/no-ex-assign
        "no-extra-boolean-cast": 0,         // http://eslint.org/docs/rules/no-extra-boolean-cast
        "no-extra-semi": 2,                 // http://eslint.org/docs/rules/no-extra-semi
        "no-func-assign": 2,                // http://eslint.org/docs/rules/no-func-assign
        "no-inner-declarations": 2,         // http://eslint.org/docs/rules/no-inner-declarations
        "no-invalid-regexp": 2,             // http://eslint.org/docs/rules/no-invalid-regexp
        "no-irregular-whitespace": 2,       // http://eslint.org/docs/rules/no-irregular-whitespace
        "no-obj-calls": 2,                  // http://eslint.org/docs/rules/no-obj-calls
        "no-sparse-arrays": 2,              // http://eslint.org/docs/rules/no-sparse-arrays
        "no-unreachable": 2,                // http://eslint.org/docs/rules/no-unreachable
        "use-isnan": 2,                     // http://eslint.org/docs/rules/use-isnan
        "block-scoped-var": 2,              // http://eslint.org/docs/rules/block-scoped-var
        "valid-typeof": 2,                  // http://eslint.org/docs/rules/valid-typeof
        /**
         * Best practices
         */
        "array-callback-return": [2, {      // http://eslint.org/docs/rules/array-callback-return
            allowImplicit: true,
        }],
        "consistent-return": 1,             // http://eslint.org/docs/rules/consistent-return
        curly: [2, "multi-line"],           // http://eslint.org/docs/rules/curly
        "default-case": 2,                  // http://eslint.org/docs/rules/default-case
        "dot-notation": [2, {               // http://eslint.org/docs/rules/dot-notation
            allowKeywords: true,
        }],
        "linebreak-style": [2, "unix"],     // http://eslint.org/docs/rules/linebreak-style
        eqeqeq: 2,                          // http://eslint.org/docs/rules/eqeqeq
        "guard-for-in": 0,                  // http://eslint.org/docs/rules/guard-for-in
        "no-array-constructor": 2,          // http://eslint.org/docs/rules/no-array-constructor
        "no-caller": 2,                     // http://eslint.org/docs/rules/no-caller
        "no-else-return": 2,                // http://eslint.org/docs/rules/no-else-return
        "no-eq-null": 2,                    // http://eslint.org/docs/rules/no-eq-null
        "no-eval": 2,                       // http://eslint.org/docs/rules/no-eval
        "no-extend-native": 2,              // http://eslint.org/docs/rules/no-extend-native
        "no-extra-bind": 2,                 // http://eslint.org/docs/rules/no-extra-bind
        "no-fallthrough": 2,                // http://eslint.org/docs/rules/no-fallthrough
        "no-floating-decimal": 2,           // http://eslint.org/docs/rules/no-floating-decimal
        "no-implied-eval": 2,               // http://eslint.org/docs/rules/no-implied-eval
        "no-lone-blocks": 2,                // http://eslint.org/docs/rules/no-lone-blocks
        "no-loop-func": 2,                  // http://eslint.org/docs/rules/no-loop-func
        "no-multi-str": 2,                  // http://eslint.org/docs/rules/no-multi-str
        "no-native-reassign": 2,            // http://eslint.org/docs/rules/no-native-reassign
        "no-new": 2,                        // http://eslint.org/docs/rules/no-new
        "no-new-func": 2,                   // http://eslint.org/docs/rules/no-new-func
        "no-new-wrappers": 2,               // http://eslint.org/docs/rules/no-new-wrappers
        "no-octal": 2,                      // http://eslint.org/docs/rules/no-octal
        "no-octal-escape": 2,               // http://eslint.org/docs/rules/no-octal-escape
        "no-param-reassign": 2,             // http://eslint.org/docs/rules/no-param-reassign
        "no-proto": 2,                      // http://eslint.org/docs/rules/no-proto
        "no-prototype-builtins": 1,         // http://eslint.org/docs/rules/no-prototype-builtins
        "no-redeclare": 2,                  // http://eslint.org/docs/rules/no-redeclare
        "no-return-assign": 2,              // http://eslint.org/docs/rules/no-return-assign
        "no-script-url": 2,                 // http://eslint.org/docs/rules/no-script-url
        "no-self-compare": 2,               // http://eslint.org/docs/rules/no-self-compare
        "no-sequences": 2,                  // http://eslint.org/docs/rules/no-sequences
        "no-throw-literal": 2,              // http://eslint.org/docs/rules/no-throw-literal
        "no-with": 2,                       // http://eslint.org/docs/rules/no-with
        radix: 2,                           // http://eslint.org/docs/rules/radix
        "vars-on-top": 2,                   // http://eslint.org/docs/rules/vars-on-top
        "wrap-iife": [2, "any"],            // http://eslint.org/docs/rules/wrap-iife
        "object-shorthand": [2, "always", { // http://eslint.org/docs/rules/object-shorthand
            ignoreConstructors: true,
            avoidQuotes: true,
        }],
        "quote-props": [2, "as-needed", {   // http://eslint.org/docs/rules/quote-props
            keywords: true,
        }],
        yoda: 2,                            // http://eslint.org/docs/rules/yoda
        /**
         * Style
         */
        indent: [2, 4, {                    // http://eslint.org/docs/rules/indent
            SwitchCase: 1,
        }],
        "brace-style": [2,                  // http://eslint.org/docs/rules/brace-style
            "stroustrup", {
                allowSingleLine: true,
            },
        ],
        quotes: [                           // http://eslint.org/docs/rules/quotes
            2, "double", "avoid-escape",
        ],
        camelcase: [2, {                    // http://eslint.org/docs/rules/camelcase
            properties: "never",
        }],
        "comma-spacing": [2, {              // http://eslint.org/docs/rules/comma-spacing
            before: false,
            after: true,
        }],
        "comma-style": [2, "last"],         // http://eslint.org/docs/rules/comma-style
        "eol-last": 2,                      // http://eslint.org/docs/rules/eol-last
        "func-names": 0,                    // http://eslint.org/docs/rules/func-names
        "key-spacing": [2, {                // http://eslint.org/docs/rules/key-spacing
            beforeColon: false,
            afterColon: true,
        }],
        "no-multiple-empty-lines": [2, {    // http://eslint.org/docs/rules/no-multiple-empty-lines
            max: 2,
        }],
        "no-nested-ternary": 2,             // http://eslint.org/docs/rules/no-nested-ternary
        "no-new-object": 2,                 // http://eslint.org/docs/rules/no-new-object
        "no-spaced-func": 2,                // http://eslint.org/docs/rules/no-spaced-func
        "no-trailing-spaces": 2,            // http://eslint.org/docs/rules/no-trailing-spaces
        "no-extra-parens": [2,              // http://eslint.org/docs/rules/no-extra-parens
            "functions",
        ],
        "no-underscore-dangle": 0,          // http://eslint.org/docs/rules/no-underscore-dangle
        "one-var": [2, "never"],            // http://eslint.org/docs/rules/one-var
        "padded-blocks": [2, "never"],      // http://eslint.org/docs/rules/padded-blocks
        semi: [2, "always"],                // http://eslint.org/docs/rules/semi
        "semi-spacing": [2, {               // http://eslint.org/docs/rules/semi-spacing
            before: false,
            after: true,
        }],
        "space-after-keywords": 0,          // http://eslint.org/docs/rules/space-after-keywords
        "keyword-spacing": [0, {            // http://eslint.org/docs/rules/keyword-spacing
            before: false,
            after: true,
        }],
        "space-before-function-paren": [2,  // http://eslint.org/docs/rules/space-before-function-paren
            "never",
        ],
        "space-infix-ops": 2,               // http://eslint.org/docs/rules/space-infix-ops
        "space-return-throw-case": 0,       // http://eslint.org/docs/rules/space-return-throw-case
        "spaced-comment": 2,                // http://eslint.org/docs/rules/spaced-comment
        "@typescript-eslint/explicit-function-return-type": "warn",
        "@typescript-eslint/no-explicit-any": "warn",
        "@typescript-eslint/no-non-null-assertion": 0,
    },
}];
