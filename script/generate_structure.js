var fs = require('fs');

function createFile(filename) {
    fs.writeFile(`${filename}.lagda.md`, '\n',()=>{});
}

const parts = [[
    "Naturals",
    "Induction",
    "Relations",
    "Equality",
    "Isomorphism",
    "Connectives",
    "Negation",
    "Quantifiers",
    "Decidable",
    "Lists",
],
[
    "Lambda",
    "Properties",
    "DeBruijn",
    "More",
    "Bisimulation",
    "Inference",
    "Untyped",
    "Confluence",
    "BigStep",
],
[
    "Denotational",
    "Compositional",
    "Soundness",
    "Adequacy",
    "ContextualEquivalence",]]

parts.forEach((namelist,index)=>{
    namelist.forEach((name)=>{
        createFile(`../src/part${index+1}/${name}`);
    })
})