/* global React ReactDOM */
import {sfConn, apiVersion} from "./inspector.js";
import {PageHeader} from "./components/PageHeader.js";
import {UserInfoModel} from "./utils.js";
/* global initButton */

const MIN_DEPTH = 1;
const MAX_DEPTH = 7;
const DEFAULT_DEPTH = 3;
const MAX_RECORDS = 2000; // Cap on unique records, protects the org (API calls) and the browser (rows)
const MAX_PATHS_PER_RECORD = 20;
const PATH_ENUMERATION_LIMIT = 1000; // Stop counting paths of one record after this many
const PATH_SEARCH_BUDGET = 5000; // Max recursion steps when searching the paths of one record
const LOOKUP_IDS_PER_QUERY = 200;
const RECORD_IDS_PER_QUERY = 100;
const FIELDS_CHARS_PER_QUERY = 4000;
const CONCURRENCY = 5;
const MAX_RENDERED_ROWS = 2000;
const MAX_SHOWN_WARNINGS = 20;

class CancelledError extends Error {}

// ---------------------------------------------------------------------------------------------
// Which child objects are walked.
// By default only custom objects and core CRM objects are followed; everything else (History, Share, Feed,
// platform and industry cloud objects, ...) explodes the number of API calls. The lists below are meant to be extended.
// "Include system relationships" turns the allow-list and noise filtering off (see isChildWalkable).
// ---------------------------------------------------------------------------------------------
const NOISE_SUFFIXES = ["History", "Share", "Feed", "ChangeEvent", "__hd", "__e", "__x", "__mdt", "Tag", "OwnerSharingRule"];
const NOISE_PREFIXES = ["ProcessInstance", "RecordAction"];
const NOISE_NAMES = new Set([
  "OutgoingEmail", "ActivityHistory", "OpenActivity", "AttachedContentDocument", "CombinedAttachment", "EmailStatus",
  "NoteAndAttachment", "LookedUpFromActivity", "AttachedContentNote", "FeedComment", "FeedItem", "EntitySubscription",
  "Vote", "TopicAssignment", "FlowRecordRelation", "FlowExecutionErrorEvent", "ContentDistribution", "ContentDocumentLink",
  "ContentVersion", "PendingServiceRouting", "PendingServiceRoutingInteractionInfo", "AgentWork", "UserPrioritizedRecord",
  "AIInsightValue", "AIRecordInsight", "AuthProvider", "UserRole",
  // Task/Event WhatId-WhoId queries are often rewritten as OR, can be unsupported, and can hang for minutes
  "Task", "Event", "EventRelation",
  // High-cost on every parent at every layer; shown only when "Include system relationships" is on
  "Note", "Attachment", "EmailMessage", "Partner", "AccountPartner", "OpportunityPartner",
  "AccountContactRole", "AccountTeamMember", "User"
]);
// Standard objects that are walked when system relationships are excluded. Custom objects are always walked.
const KEEP_STANDARD_NAMES = new Set([
  "Account", "Contact", "Lead", "Opportunity", "OpportunityLineItem", "OpportunityContactRole", "AccountContactRelation",
  "Case", "CaseComment", "Contract", "Asset",
  "Order", "OrderItem", "Quote", "QuoteLineItem", "Campaign", "CampaignMember", "Product2", "PricebookEntry",
]);
// Used as a first guess so the walk can SELECT the name field before the object has been described.
const KNOWN_NAME_FIELDS = {Case: "CaseNumber", Task: "Subject", Event: "Subject", Contract: "ContractNumber"};

function isNoiseObjectName(name) {
  return NOISE_NAMES.has(name)
    || NOISE_SUFFIXES.some(suffix => name.endsWith(suffix))
    || NOISE_PREFIXES.some(prefix => name.startsWith(prefix));
}

function isCustomObject(name, info) {
  return Boolean(info && info.custom) || name.includes("__c");
}

function isOrUnsupportedError(err) {
  let message = String((err && err.message) || err);
  return /UNSUPPORTED_QUERY/i.test(message) || /operator OR/i.test(message);
}

function clampDepth(value) {
  let n = parseInt(value, 10);
  if (isNaN(n)) {
    return DEFAULT_DEPTH;
  }
  return Math.min(MAX_DEPTH, Math.max(MIN_DEPTH, n));
}

function soqlString(value) {
  return "'" + String(value).replace(/[\\']/g, "\\$&") + "'";
}

// Salesforce 15- and 18-character Ids identify the same record; maps and edge lookups use the first 15.
function shortId(id) {
  return id ? String(id).substring(0, 15) : "";
}

function chunk(list, size) {
  let chunks = [];
  for (let i = 0; i < list.length; i += size) {
    chunks.push(list.slice(i, i + size));
  }
  return chunks;
}

function formatValue(value) {
  if (value === null || value === undefined) {
    return "";
  }
  if (typeof value == "object") {
    return JSON.stringify(value);
  }
  return String(value);
}

class Model {
  constructor(sfHost, sobjectName, recordId, includeSystem) {
    this.reactCallback = null;
    this.sfHost = sfHost;
    this.sfLink = "https://" + sfHost;
    this.orgName = sfHost.split(".")[0]?.toUpperCase() || "";
    this.spinnerCount = 0;
    this.errorMessages = [];
    this.sobjectName = sobjectName;
    this.recordId = recordId;

    this.depthInput = String(DEFAULT_DEPTH);
    this.includeSystem = includeSystem;
    this.rowsFilter = "";
    this.userInfoModel = new UserInfoModel((promise) => {
      this.spinnerCount++;
      promise
        .then(() => {
          this.spinnerCount--;
          this.didUpdate();
        })
        .catch(err => {
          console.error(err);
          this.errorMessages.push("Error retrieving user info: " + err.message);
          this.spinnerCount--;
          this.didUpdate();
        })
        .catch(err => console.log("error handling failed", err));
    });

    this.describeCache = new Map(); // object API name -> Promise of describe (null when it failed)
    this.globalPromise = null; // describeGlobal, requested once per page session
    this.nameFields = new Map(); // object API name -> name field to query (null when the object has none), unknown when absent
    this.resetRun();
  }

  resetRun() {
    this.running = false;
    this.cancelled = false;
    this.stoppedEarly = false;
    this.finished = false;
    this.capHit = false;
    this.errorMessages = [];
    this.depth = DEFAULT_DEPTH;
    this.currentLayer = 0;
    this.apiCalls = 0;
    this.warnings = [];
    this.warnKeys = new Set();
    this.unsupported = new Set(); // child objects whose queries failed, skipped for the rest of the walk
    this.singleIdObjects = new Set(); // child objects that must be queried with one Id per query
    this.phase = "";
    this.edgeVersion = 0;
    this.pathCache = new Map();
    this.pathCacheVersion = 0;
    this.lastRender = 0;
    if (this.updateTimer) {
      clearTimeout(this.updateTimer);
    }
    this.updateTimer = null;
    this.rootId = null;
    this.records = new Map(); // id -> {id, object, layer}
    this.edges = new Map(); // child id -> [{parentId, step}]
    this.values = new Map(); // id -> {fieldName: value}
    this.rows = [];
  }

  didUpdate(cb) {
    if (this.reactCallback) {
      this.reactCallback(cb);
    }
  }

  // Stops new API calls at once (api() throws), requests already in flight may still finish. Shows what was collected so far.
  cancel() {
    this.cancelled = true;
    this.stoppedEarly = true;
    this.buildRows();
    this.didUpdate();
  }

  // Throttled re-render, used for the frequent API call counter
  scheduleUpdate() {
    if (this.updateTimer) {
      return;
    }
    this.updateTimer = setTimeout(() => {
      this.updateTimer = null;
      this.didUpdate();
    }, 250);
  }

  // Rebuilds the rows and re-renders, at most once per second unless forced
  refreshRows(force) {
    if (force || Date.now() - this.lastRender > 1000) {
      this.lastRender = Date.now();
      this.buildRows();
      this.didUpdate();
    }
  }

  // Every API call goes through here so they are counted and no new one starts after Cancel
  async api(url) {
    if (this.cancelled) {
      throw new CancelledError("Cancelled");
    }
    this.apiCalls++;
    this.scheduleUpdate();
    return sfConn.rest(url, {logErrors: false});
  }

  // Warnings are deduped: the same message is only listed once
  warn(message) {
    if (!this.warnKeys.has(message)) {
      this.warnKeys.add(message);
      this.warnings.push(message);
    }
  }

  // describeGlobal, once. Resolves to Map name -> flags, or null when it failed (name rules only are used then).
  describeGlobal() {
    if (!this.globalPromise) {
      this.globalPromise = this.api("/services/data/v" + apiVersion + "/sobjects")
        .then(res => new Map(res.sobjects.map(o => [o.name, o])))
        .catch(err => {
          if (err instanceof CancelledError) {
            this.globalPromise = null;
            throw err;
          }
          this.warn("describeGlobal failed: " + (err.message || err));
          return null;
        });
    }
    return this.globalPromise;
  }

  markUnsupported(object) {
    this.unsupported.add(object);
    this.warn(object + ": query not supported, skipped");
  }

  // Decides if the child object of a relationship is queried. See the lists at the top of the file.
  isChildWalkable(rel, globalInfo) {
    let name = rel.childSObject;
    if (!rel.relationshipName || rel.deprecatedAndHidden || this.unsupported.has(name)) {
      return false;
    }
    let info = globalInfo ? globalInfo.get(name) : null;
    if (globalInfo && (!info || !info.queryable || info.deprecatedAndHidden)) {
      return false;
    }
    if (this.includeSystem) {
      return true;
    }
    if (info && !info.retrieveable) {
      return false;
    }
    if (isNoiseObjectName(name)) {
      return false;
    }
    return isCustomObject(name, info) || KEEP_STANDARD_NAMES.has(name);
  }

  describe(name) {
    if (!this.describeCache.has(name)) {
      this.describeCache.set(name, this.api("/services/data/v" + apiVersion + "/sobjects/" + encodeURIComponent(name) + "/describe")
        .then(describe => {
          let nameField = describe.fields.find(f => f.nameField);
          this.nameFields.set(describe.name, nameField ? nameField.name : null);
          return describe;
        })
        .catch(err => {
          if (err instanceof CancelledError) {
            this.describeCache.delete(name);
            throw err;
          }
          this.warn("Describe of " + name + " failed: " + (err.message || err));
          return null;
        }));
    }
    return this.describeCache.get(name);
  }

  // Runs the query and follows nextRecordsUrl so no page is dropped
  async queryAll(query) {
    let records = [];
    let res = await this.api("/services/data/v" + apiVersion + "/query/?q=" + encodeURIComponent(query));
    records.push(...res.records);
    while (res.nextRecordsUrl) {
      res = await this.api(res.nextRecordsUrl);
      records.push(...res.records);
    }
    return records;
  }

  // Runs async tasks with limited concurrency. A failing task is recorded as a warning, cancellation stops everything.
  async runPool(tasks, describeTask) {
    let next = 0;
    let cancelledError = null;
    let worker = async () => {
      while (next < tasks.length && !this.cancelled && !this.capHit && !cancelledError) {
        let task = tasks[next++];
        try {
          await task();
        } catch (err) {
          if (err instanceof CancelledError) {
            cancelledError = err;
          } else {
            this.warn(describeTask + ": " + (err.message || err));
          }
        }
      }
    };
    await Promise.all(Array.from({length: Math.min(CONCURRENCY, tasks.length)}, worker));
    if (cancelledError) {
      throw cancelledError;
    }
  }

  hasValidTarget() {
    return Boolean(this.sobjectName) && /^[a-zA-Z0-9]{15,18}$/.test(this.recordId || "");
  }

  async run() {
    if (this.running || !this.hasValidTarget()) {
      return;
    }
    this.resetRun();
    this.depth = clampDepth(this.depthInput);
    this.depthInput = String(this.depth);
    this.running = true;
    this.finished = false;
    this.spinnerCount++;
    this.didUpdate();
    try {
      try {
        await this.walk();
      } catch (err) {
        if (!(err instanceof CancelledError)) {
          throw err;
        }
      }
      // Fields are loaded after the walk, never after Cancel. The table is already filled with Id and Name by then.
      if (this.records.size > 0 && !this.cancelled) {
        this.phase = "Loading fields";
        this.refreshRows(true);
        await this.loadFieldValues();
      }
    } catch (err) {
      if (!(err instanceof CancelledError)) {
        console.error(err);
        this.errorMessages.push("Error walking child relationships: " + (err.message || err));
      }
    } finally {
      this.running = false;
      this.finished = true;
      this.phase = "";
      this.spinnerCount--;
      this.buildRows();
      this.didUpdate();
    }
  }

  // Stores the values that were selected, so the table can show them while the walk is still running
  mergeValues(id, rec) {
    let key = shortId(id);
    let values = this.values.get(key) || {};
    for (let name of Object.keys(rec)) {
      if (name != "attributes") {
        values[name] = rec[name];
      }
    }
    this.values.set(key, values);
  }

  // Queries the children of one chunk of parent Ids with a single IN (never OR). Selects the name field when it is known or likely.
  async queryChildren(rel, ids) {
    let object = rel.childSObject;
    let build = nameField => {
      let fields = ["Id"];
      if (nameField && nameField != "Id" && nameField != rel.field) {
        fields.push(nameField);
      }
      fields.push(rel.field);
      return "SELECT " + fields.join(", ") + " FROM " + object + " WHERE " + rel.field + " IN (" + ids.map(soqlString).join(",") + ")";
    };
    let nameField = this.nameFields.has(object) ? this.nameFields.get(object) : (KNOWN_NAME_FIELDS[object] || "Name");
    try {
      return await this.queryAll(build(nameField));
    } catch (err) {
      if (nameField && !(err instanceof CancelledError) && /No such column/i.test(String(err.message))) {
        this.nameFields.set(object, null);
        return await this.queryAll(build(null));
      }
      throw err;
    }
  }

  // Queries the children of the given parents. If the multi Id query fails because the object does not support it,
  // the object is retried once with one Id per query. Any other failure marks the object unsupported.
  async queryChildChunk(rel, ids) {
    let object = rel.childSObject;
    let children = [];
    let groups = this.singleIdObjects.has(object) ? ids.map(id => [id]) : [ids];
    for (let group of groups) {
      if (this.unsupported.has(object)) {
        break;
      }
      try {
        children.push(...await this.queryChildren(rel, group));
      } catch (err) {
        if (err instanceof CancelledError) {
          throw err;
        }
        if (group.length > 1 && isOrUnsupportedError(err) && !this.singleIdObjects.has(object)) {
          this.singleIdObjects.add(object);
          return await this.queryChildChunk(rel, ids);
        }
        this.markUnsupported(object);
        break;
      }
    }
    return children;
  }

  async walk() {
    let globalInfo = await this.describeGlobal();
    let rootDescribe = await this.describe(this.sobjectName);
    if (!rootDescribe) {
      throw new Error("Cannot describe " + this.sobjectName);
    }
    // Query the root to validate it exists and to get its 18 character Id
    let rootName = this.nameFields.get(rootDescribe.name);
    let rootRecords = await this.queryAll("SELECT Id" + (rootName && rootName != "Id" ? ", " + rootName : "") + " FROM " + rootDescribe.name + " WHERE Id = " + soqlString(this.recordId));
    if (rootRecords.length == 0) {
      throw new Error("Record " + this.recordId + " not found in " + rootDescribe.name);
    }
    this.rootId = rootRecords[0].Id;
    let rootKey = shortId(this.rootId);
    this.records.set(rootKey, {id: this.rootId, object: rootDescribe.name, layer: 0});
    this.mergeValues(this.rootId, rootRecords[0]);
    this.refreshRows(true);

    // Breadth first: each layer is queried per relationship, for all the records of the previous layer at once
    let frontier = [rootKey];
    for (let layer = 1; layer <= this.depth && frontier.length > 0 && !this.capHit; layer++) {
      this.currentLayer = layer;
      this.didUpdate();
      let nextFrontier = [];

      let idsByObject = new Map();
      for (let key of frontier) {
        let object = this.records.get(key).object;
        if (!idsByObject.has(object)) {
          idsByObject.set(object, []);
        }
        idsByObject.get(object).push(key);
      }

      // Only the objects that are expanded are described, child objects are judged from describeGlobal
      let parentDescribes = new Map();
      for (let object of idsByObject.keys()) {
        parentDescribes.set(object, await this.describe(object));
      }

      let queryTasks = [];
      for (let [object, ids] of idsByObject) {
        let describe = parentDescribes.get(object);
        for (let rel of describe ? describe.childRelationships : []) {
          if (!this.isChildWalkable(rel, globalInfo)) {
            continue;
          }
          let parentKeys = new Set(ids);
          let fullIds = ids.map(key => this.records.get(key).id);
          for (let idsChunk of chunk(fullIds, LOOKUP_IDS_PER_QUERY)) {
            queryTasks.push(async () => {
              let children = await this.queryChildChunk(rel, idsChunk);
              for (let child of children) {
                let parentKey = shortId(child[rel.field]);
                if (parentKeys.has(parentKey)) {
                  if (this.addChild(parentKey, child.Id, rel, layer, nextFrontier)) {
                    this.mergeValues(child.Id, child);
                  }
                }
              }
            });
          }
        }
      }
      try {
        await this.runPool(queryTasks, "Query children");
      } finally {
        this.refreshRows(true);
      }
      frontier = nextFrontier;
    }
  }

  // Records the edge parent -> child. A record that is already known is never added to the next frontier again,
  // which is what breaks cycles; its extra edge is kept so every path can be listed.
  addChild(parentKey, childId, rel, layer, nextFrontier) {
    let childKey = shortId(childId);
    let isNew = !this.records.has(childKey);
    if (isNew) {
      if (this.records.size >= MAX_RECORDS) {
        this.capHit = true;
        return false;
      }
      this.records.set(childKey, {id: childId, object: rel.childSObject, layer});
      nextFrontier.push(childKey);
    }
    let step = rel.relationshipName + "." + rel.field;
    if (!this.edges.has(childKey)) {
      this.edges.set(childKey, []);
    }
    let edgeList = this.edges.get(childKey);
    if (!edgeList.some(e => e.parentId === parentKey && e.step === step)) {
      edgeList.push({parentId: parentKey, step});
      this.edgeVersion++;
    }
    return isNew;
  }

  fieldsToQuery(describe) {
    return describe.fields
      .filter(f => !f.deprecatedAndHidden
        && f.type != "address" && f.type != "location" // compound parents, their constituents have compoundFieldName and are queried instead
        && f.type != "base64") // blobs can only be queried one record at a time
      .map(f => f.name);
  }

  async loadFieldValues() {
    let idsByObject = new Map();
    for (let record of this.records.values()) {
      if (!idsByObject.has(record.object)) {
        idsByObject.set(record.object, []);
      }
      idsByObject.get(record.object).push(record.id);
    }
    let tasks = [];
    for (let [object, ids] of idsByObject) {
      let describe = await this.describe(object);
      if (!describe) {
        continue;
      }
      let names = this.fieldsToQuery(describe).filter(name => name != "Id");
      // Split the fields so each query stays below the query length limit, Id is always selected
      let fieldChunks = [];
      let current = [];
      let length = 0;
      for (let name of names) {
        if (length + name.length + 1 > FIELDS_CHARS_PER_QUERY && current.length > 0) {
          fieldChunks.push(current);
          current = [];
          length = 0;
        }
        current.push(name);
        length += name.length + 1;
      }
      fieldChunks.push(current);
      for (let idsChunk of chunk(ids, RECORD_IDS_PER_QUERY)) {
        for (let fields of fieldChunks) {
          tasks.push(async () => {
            let query = "SELECT " + ["Id", ...fields].join(",") + " FROM " + object + " WHERE Id IN (" + idsChunk.map(soqlString).join(",") + ")";
            for (let rec of await this.queryAll(query)) {
              this.mergeValues(rec.Id, rec);
            }
            this.refreshRows(false);
          });
        }
      }
    }
    // Fields are needed for every record found, so the record cap must not stop this phase
    let capHit = this.capHit;
    this.capHit = false;
    try {
      await this.runPool(tasks, "Query fields");
    } finally {
      this.capHit = capHit;
    }
  }

  // All simple paths from the root to a record, searched backwards over the recorded edges
  pathsFor(id) {
    let rootKey = shortId(this.rootId);
    let label = key => {
      let rec = this.records.get(key);
      return rec.object + "(" + rec.id + ")";
    };
    if (this.pathCacheVersion != this.edgeVersion) {
      this.pathCache = new Map();
      this.pathCacheVersion = this.edgeVersion;
    }
    if (this.pathCache.has(id)) {
      return this.pathCache.get(id);
    }
    let paths = [];
    let total = 0;
    let budget = PATH_SEARCH_BUDGET;
    let visited = new Set();
    let search = (nodeId, tail) => {
      if (budget-- <= 0 || total >= PATH_ENUMERATION_LIMIT) {
        return;
      }
      if (nodeId === rootKey) {
        total++;
        if (paths.length < MAX_PATHS_PER_RECORD) {
          paths.push(label(nodeId) + tail.join(""));
        }
        return;
      }
      visited.add(nodeId);
      for (let edge of this.edges.get(nodeId) || []) {
        if (!visited.has(edge.parentId)) {
          search(edge.parentId, [" > " + edge.step + " > " + label(nodeId), ...tail]);
        }
      }
      visited.delete(nodeId);
    };
    search(shortId(id), []);
    if (total > paths.length) {
      paths.push("(+" + (total - paths.length) + (total >= PATH_ENUMERATION_LIMIT ? "+" : "") + " more paths truncated)");
    }
    let result = paths.join("\n");
    this.pathCache.set(id, result);
    return result;
  }

  // Emits a row for every loaded value of every collected record, so a record is listed even if only its Id is known
  buildRows() {
    let rows = [];
    for (let record of this.records.values()) {
      let values = this.values.get(shortId(record.id)) || {Id: record.id};
      let path = this.pathsFor(record.id);
      for (let name of Object.keys(values)) {
        rows.push({
          key: record.id + "." + name,
          field: name,
          value: formatValue(values[name]),
          object: record.object,
          layer: record.layer,
          id: record.id,
          path
        });
      }
    }
    let fieldRank = field => field == "Id" ? 0 : 1;
    rows.sort((a, b) => a.layer - b.layer
      || a.object.localeCompare(b.object)
      || a.id.localeCompare(b.id)
      || fieldRank(a.field) - fieldRank(b.field)
      || a.field.localeCompare(b.field));
    this.rows = rows;
  }

  filteredRows() {
    let filter = this.rowsFilter.trim().toLowerCase();
    if (!filter) {
      return this.rows;
    }
    return this.rows.filter(r => [r.field, r.value, r.object, r.path].some(text => text.toLowerCase().includes(filter)));
  }
}

let h = React.createElement;

class App extends React.Component {
  constructor(props) {
    super(props);
    this.onDepthChange = this.onDepthChange.bind(this);
    this.onDepthBlur = this.onDepthBlur.bind(this);
    this.onRun = this.onRun.bind(this);
    this.onCancel = this.onCancel.bind(this);
    this.onFilterChange = this.onFilterChange.bind(this);
    this.onIncludeSystemChange = this.onIncludeSystemChange.bind(this);
    this.onToggleWarnings = this.onToggleWarnings.bind(this);
    this.state = {warningsOpen: null}; // null: open when there are at most 3 warnings
  }

  onIncludeSystemChange(e) {
    let {model} = this.props;
    model.includeSystem = e.target.checked;
    let args = new URLSearchParams(location.search.slice(1));
    if (model.includeSystem) {
      args.set("includeSystem", "1");
    } else {
      args.delete("includeSystem");
    }
    history.replaceState(null, "", "?" + args.toString());
    model.didUpdate();
  }

  onToggleWarnings(open) {
    this.setState({warningsOpen: open});
  }

  renderWarnings(warnings) {
    let open = this.state.warningsOpen === null ? warnings.length <= 3 : this.state.warningsOpen;
    let shown = warnings.slice(0, MAX_SHOWN_WARNINGS);
    return h("div", {className: "slds-notify slds-notify_alert slds-alert_warning slds-m-horizontal_small", role: "status", style: {display: "block"}},
      h("button", {className: "slds-button", "aria-expanded": String(open), onClick: () => this.onToggleWarnings(!open)},
        (open ? "\u25BE " : "\u25B8 ") + warnings.length + (warnings.length == 1 ? " warning" : " warnings")),
      open ? h("ul", {className: "slds-m-left_large"},
        shown.map((message, index) => h("li", {key: index}, message)),
        warnings.length > shown.length ? h("li", {key: "more"}, "... and " + (warnings.length - shown.length) + " more warnings") : null
      ) : null
    );
  }

  onDepthChange(e) {
    this.props.model.depthInput = e.target.value;
    this.props.model.didUpdate();
  }

  onDepthBlur() {
    this.props.model.depthInput = String(clampDepth(this.props.model.depthInput));
    this.props.model.didUpdate();
  }

  onRun() {
    this.props.model.run();
  }

  onCancel() {
    this.props.model.cancel();
  }

  onFilterChange(e) {
    this.props.model.rowsFilter = e.target.value;
    this.props.model.didUpdate();
  }

  renderStatus(model) {
    let parts = [];
    if (model.running || model.finished) {
      parts.push("Records: " + model.records.size);
      parts.push("Layer: " + model.currentLayer + " / " + model.depth);
      parts.push("API calls: " + model.apiCalls);
    }
    if (model.running) {
      parts.push(model.cancelled ? "Cancelling..." : (model.phase ? "Running (" + model.phase.toLowerCase() + ")..." : "Running..."));
    } else if (model.finished) {
      parts.push(model.stoppedEarly ? "Cancelled, partial results" : "Done");
    }
    return parts.join(" | ");
  }

  renderAlert(className, icon, messages) {
    return h("div", {className: "slds-notify_container slds-is-relative"},
      h("div", {className: "slds-notify slds-notify_alert " + className, role: "status"},
        h("span", {className: "slds-icon_container slds-m-right_small slds-no-flex slds-align-top"},
          h("svg", {className: "slds-icon slds-icon_small", "aria-hidden": "true"},
            h("use", {xlinkHref: "symbols.svg#" + icon})
          )
        ),
        h("div", {className: "slds-notify__content"},
          messages.map((message, index) => h("h2", {className: "slds-text-heading_small", key: index}, message))
        )
      )
    );
  }

  render() {
    let {model} = this.props;
    document.title = "Child Tree - " + model.sobjectName;
    let rows = model.filteredRows();
    let shownRows = rows.slice(0, MAX_RENDERED_ROWS);
    return h("div", {},
      h(PageHeader, {
        pageTitle: "Child Tree",
        subTitle: model.sobjectName + " " + model.recordId,
        orgName: model.orgName,
        sfLink: model.sfLink,
        sfHost: model.sfHost,
        spinnerCount: model.spinnerCount,
        ...model.userInfoModel.getProps()
      }),
      h("div", {className: "slds-m-top_xx-large sfir-page-container"},
        h("div", {className: "slds-card slds-m-around_medium", style: {flex: "1 1 0", display: "flex", flexDirection: "column", minHeight: 0}},
          model.errorMessages.length > 0 ? this.renderAlert("slds-alert_error", "error", model.errorMessages) : null,
          model.capHit ? this.renderAlert("slds-alert_warning", "warning", ["Stopped expanding after " + MAX_RECORDS + " unique records. Results are incomplete, try a lower depth."]) : null,
          model.warnings.length > 0 ? this.renderWarnings(model.warnings) : null,
          h("div", {className: "slds-card__header slds-grid slds-grid_vertical-align-center slds-p-around_small"},
            h("div", {className: "slds-form-element slds-m-right_small"},
              h("label", {className: "slds-form-element__label", htmlFor: "depth"}, "Depth (" + MIN_DEPTH + "-" + MAX_DEPTH + ")"),
              h("div", {className: "slds-form-element__control"},
                h("input", {
                  id: "depth",
                  className: "slds-input",
                  type: "number",
                  min: MIN_DEPTH,
                  max: MAX_DEPTH,
                  style: {width: "5rem"},
                  value: model.depthInput,
                  disabled: model.running,
                  onChange: this.onDepthChange,
                  onBlur: this.onDepthBlur
                })
              )
            ),
            h("div", {className: "slds-form-element slds-m-right_small"},
              h("div", {className: "slds-form-element__control"},
                h("label", {className: "slds-checkbox"},
                  h("input", {id: "includeSystem", type: "checkbox", checked: model.includeSystem, disabled: model.running, onChange: this.onIncludeSystemChange}),
                  h("span", {className: "slds-checkbox_faux"}),
                  h("span", {className: "slds-form-element__label"}, "Include system relationships")
                )
              )
            ),
            h("button", {className: "slds-button slds-button_brand slds-m-right_x-small", disabled: model.running || !model.hasValidTarget(), onClick: this.onRun, title: "Walk the descendant child records down to the chosen depth"}, "Run"),
            h("button", {className: "slds-button slds-button_neutral slds-m-right_small", disabled: !model.running || model.cancelled, onClick: this.onCancel, title: "Stop starting new queries"}, "Cancel"),
            h("input", {className: "slds-input slds-m-right_small", style: {maxWidth: "20rem"}, placeholder: "Filter", value: model.rowsFilter, onChange: this.onFilterChange}),
            h("span", {className: "slds-text-body_small"}, this.renderStatus(model))
          ),
          rows.length > shownRows.length
            ? h("div", {className: "slds-p-horizontal_small slds-text-body_small"}, "Showing the first " + shownRows.length + " of " + rows.length + " rows, use the filter to narrow down.")
            : null,
          h("div", {className: "sfir-tree-table-wrapper"},
            h("table", {className: "slds-table slds-table_bordered slds-table_cell-buffer sfir-tree-table"},
              h("thead", {},
                h("tr", {className: "slds-line-height_reset"},
                  ["Field", "Value", "Object", "Layer", "Path"].map(title => h("th", {key: title, scope: "col"}, h("div", {className: "slds-truncate"}, title)))
                )
              ),
              h("tbody", {},
                shownRows.map((row, index) =>
                  h("tr", {key: row.key, className: index == 0 || shownRows[index - 1].id != row.id ? "sfir-tree-first-row" : ""},
                    h("td", {}, row.field),
                    h("td", {className: "sfir-tree-value"}, row.value),
                    h("td", {}, row.object),
                    h("td", {}, row.layer),
                    h("td", {className: "sfir-tree-path"}, row.path)
                  )
                )
              )
            )
          )
        )
      )
    );
  }
}

{
  let args = new URLSearchParams(location.search.slice(1));
  let sfHost = args.get("host");
  initButton(sfHost, true);
  sfConn.getSession(sfHost).then(() => {
    let root = document.getElementById("root");
    let model = new Model(sfHost, args.get("objectType"), args.get("recordId"), args.get("includeSystem") == "1");
    if (!model.hasValidTarget()) {
      model.errorMessages.push("A valid objectType and recordId URL parameter are required.");
    }
    model.reactCallback = cb => {
      ReactDOM.render(h(App, {model}), root, cb);
    };
    ReactDOM.render(h(App, {model}), root);
  });
}
