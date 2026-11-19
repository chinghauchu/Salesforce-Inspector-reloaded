// Pure SOQL generator for the Child Tree "Selected values" feature. No DOM, no network: unit testable in node.
//
// Input shapes
//   selectionGroups: [{
//     object: "Case",                      // object API name of the selected records
//     steps: [{parentObject, childObject, relationshipName, field}, ...]
//                                          // path from the root to the object, one step per child relationship,
//                                          // field is the lookup field on childObject. Empty array: the root itself.
//     items: [{field: "Status", value: "New"}, ...]
//                                          // one item per selected row; value "" / null / undefined means null
//   }]
//   describes: {ObjectName: describeResult | null}   // sobject describes of the objects on the paths
//   rootId, rootObject
//
// Output: [{object, pathLabel, steps, warnings: [string], soql, text}]
//   soql: the query only, text: warning comment lines (`-- ...`) followed by the query

export const MAX_PARENT_HOPS = 5; // SOQL allows 5 levels of parent relationships

const UNQUOTED_TYPES = new Set(["int", "long", "double", "currency", "percent", "boolean", "date", "datetime", "time"]);
const NUMBER_TYPES = new Set(["int", "long", "double", "currency", "percent"]);
const NOT_FILTERABLE_TYPES = new Set(["address", "location", "base64"]);

export function soqlQuote(value) {
  return "'" + String(value).replace(/[\\']/g, "\\$&").replace(/\n/g, "\\n").replace(/\r/g, "\\r") + "'";
}

function isNullValue(value) {
  return value === null || value === undefined || value === "";
}

// SOQL datetime literals need a colon in the offset, the API returns +0000
function formatDateTime(value) {
  return String(value).replace(/([+-]\d\d)(\d\d)$/, "$1:$2");
}

// Formats one value as a SOQL literal depending on the field type; unknown fields are quoted
export function formatLiteral(value, type) {
  let text = String(value);
  if (type && UNQUOTED_TYPES.has(type)) {
    if (type == "boolean") {
      let lower = text.toLowerCase();
      if (lower == "true" || lower == "false") {
        return lower;
      }
    } else if (NUMBER_TYPES.has(type)) {
      if (/^[+-]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$/.test(text)) {
        return text;
      }
    } else if (type == "date") {
      if (/^\d{4}-\d{2}-\d{2}$/.test(text)) {
        return text;
      }
    } else if (type == "datetime") {
      if (/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(\.\d+)?(Z|[+-]\d{2}:?\d{2})$/.test(text)) {
        return formatDateTime(text);
      }
    } else if (type == "time") {
      if (/^\d{2}:\d{2}(:\d{2}(\.\d+)?)?Z?$/.test(text)) {
        return text.endsWith("Z") ? text : text + "Z";
      }
    }
  }
  return soqlQuote(text);
}

function findField(describe, name) {
  if (!describe || !describe.fields) {
    return null;
  }
  let lower = name.toLowerCase();
  return describe.fields.find(f => f.name.toLowerCase() == lower) || null;
}

// "Account > Contacts.AccountId > Contact > ..." style label, without record Ids
export function pathLabel(rootObject, steps) {
  return [rootObject, ...steps.map(s => s.relationshipName + "." + s.field + " > " + s.childObject)].join(" > ");
}

// Shortens a long label to keep the first and last parts
export function shortenLabel(label, max = 70) {
  if (label.length <= max) {
    return label;
  }
  let parts = label.split(" > ");
  if (parts.length > 4) {
    return parts.slice(0, 2).join(" > ") + " > … > " + parts.slice(-2).join(" > ");
  }
  return label.substring(0, max - 1) + "…";
}

// Relationship name used to go from the object holding `fieldName` to the parent. Falls back to a guess when the describe is missing.
function relationshipOf(describe, fieldName, warnings) {
  let field = findField(describe, fieldName);
  if (field && field.relationshipName) {
    if (field.referenceTo && field.referenceTo.length > 1) {
      warnings.push("polymorphic lookup " + fieldName + " (" + field.referenceTo.join(", ") + "): " + field.relationshipName + " may not allow traversing to the parent fields, query can fail");
    }
    return field.relationshipName;
  }
  let guess = fieldName.endsWith("__c") ? fieldName.slice(0, -3) + "__r" : fieldName.replace(/Id$/, "");
  warnings.push("relationship name of " + fieldName + " not found in describe, guessed " + guess);
  return guess;
}

// Builds the condition that anchors the records of a path to the root. Returns {condition, warnings, tooDeep}.
//   1 step:    AccountId = 'root'
//   n steps:   Contact.AccountId = 'root'  (n - 1 relationship hops, then the lookup field of the first step)
//   too many hops: one semi-join: <lookup of the last step> IN (SELECT Id FROM <Intermediate> WHERE <anchor of the intermediate>)
export function buildAnchor(steps, describes, rootId) {
  let warnings = [];
  if (steps.length == 0) {
    return {condition: "Id = " + soqlQuote(rootId), warnings, tooDeep: false};
  }
  // Dot notation for the records at the end of steps[0..count): relationship names from the last step up to the second one
  let dotted = count => {
    let names = [];
    for (let i = count - 1; i >= 1; i--) {
      names.push(relationshipOf(describes[steps[i].childObject], steps[i].field, warnings));
    }
    names.push(steps[0].field);
    return names.join(".");
  };
  if (steps.length - 1 <= MAX_PARENT_HOPS) {
    return {condition: dotted(steps.length) + " = " + soqlQuote(rootId), warnings, tooDeep: false};
  }
  // Semi-join: split the path at k. Inner query anchors the intermediate object (steps[0..k)), the outer query reaches
  // steps[k].field through dot notation. SOQL rejects a semi-join whose inner and outer select are on the same object type,
  // so the largest k with at most 5 hops on both sides and a different intermediate object is used.
  let n = steps.length;
  let outerObject = steps[n - 1].childObject;
  for (let k = n - 1; k >= 1; k--) {
    let intermediate = steps[k - 1].childObject;
    if (k - 1 > MAX_PARENT_HOPS || n - 1 - k > MAX_PARENT_HOPS || intermediate == outerObject) {
      continue;
    }
    let inner = dotted(k) + " = " + soqlQuote(rootId);
    let outerNames = [];
    for (let i = n - 1; i > k; i--) {
      outerNames.push(relationshipOf(describes[steps[i].childObject], steps[i].field, warnings));
    }
    outerNames.push(steps[k].field);
    let splitField = findField(describes[steps[k].childObject], steps[k].field);
    if (splitField && splitField.referenceTo && splitField.referenceTo.length > 1) {
      warnings.push("polymorphic lookup " + steps[k].field + " (" + splitField.referenceTo.join(", ") + ") in a semi-join, query can fail");
    }
    warnings.push("path has more than " + MAX_PARENT_HOPS + " parent hops, a semi-join on " + intermediate + " is used");
    return {condition: outerNames.join(".") + " IN (SELECT Id FROM " + intermediate + " WHERE " + inner + ")", warnings, tooDeep: false};
  }
  warnings.push("WARNING: path too deep, not supported by SOQL");
  return {condition: dotted(n) + " = " + soqlQuote(rootId), warnings, tooDeep: true};
}

// Condition(s) for one field: IN for several values, = null for null, (= null OR IN (...)) for both
export function buildFieldCondition(field, values, type) {
  let nonNull = [...new Set(values.filter(v => !isNullValue(v)).map(v => formatLiteral(v, type)))];
  let hasNull = values.some(isNullValue);
  let inPart = nonNull.length == 1 ? field + " = " + nonNull[0] : field + " IN (" + nonNull.join(", ") + ")";
  if (hasNull && nonNull.length > 0) {
    return "(" + field + " = null OR " + inPart + ")";
  }
  return hasNull ? field + " = null" : inPart;
}

// Builds the query of one selection group (see the file header for the shape)
export function generateQuery(group, describes, rootId, rootObject) {
  let warnings = [];
  let describe = describes[group.object];
  if (!describe) {
    warnings.push("describe of " + group.object + " not available, all values are quoted as strings");
  }
  let anchor = buildAnchor(group.steps, describes, rootId);
  warnings.push(...anchor.warnings);

  // Values per field, in order of first selection
  let valuesByField = new Map();
  for (let item of group.items) {
    if (!valuesByField.has(item.field)) {
      valuesByField.set(item.field, []);
    }
    valuesByField.get(item.field).push(item.value);
  }
  let selectFields = ["Id"];
  let conditions = [];
  for (let [name, values] of valuesByField) {
    let field = findField(describe, name);
    let notFilterable = field && (field.filterable === false || NOT_FILTERABLE_TYPES.has(field.type));
    let notSelectable = field && field.type == "base64";
    if (!selectFields.includes(name) && !notSelectable) {
      selectFields.push(name);
    }
    if (notFilterable) {
      warnings.push("note: " + name + " not filterable, not used in WHERE");
      continue;
    }
    conditions.push(buildFieldCondition(name, values, field ? field.type : null));
  }
  let soql = "SELECT " + selectFields.join(", ") + " FROM " + group.object + " WHERE " + [anchor.condition, ...conditions].join(" AND ");
  let text = [...warnings.map(w => "-- " + w), soql].join("\n");
  return {
    object: group.object,
    pathLabel: pathLabel(rootObject, group.steps),
    steps: group.steps,
    warnings,
    soql,
    text
  };
}

// Builds one query per selection group, sorted by object and path
export function generateQueries(selectionGroups, describes, rootId, rootObject) {
  return selectionGroups
    .filter(group => group.items.length > 0)
    .map(group => generateQuery(group, describes, rootId, rootObject));
}
