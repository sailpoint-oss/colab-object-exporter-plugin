package sailpoint.mcobjectexporter.task;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.Set;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Collection;
import java.util.Map;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.apache.commons.lang.StringEscapeUtils;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.w3c.dom.Document;
import org.w3c.dom.DocumentType;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.Attr;
import org.w3c.dom.NodeList;
import org.w3c.dom.Text;

import sailpoint.api.SailPointFactory;
import sailpoint.api.SailPointContext;
import sailpoint.object.Resolver;
import sailpoint.object.SailPointObject;
import sailpoint.object.Application;
import sailpoint.object.Attributes;
import sailpoint.object.AuditConfig;
import sailpoint.object.AuditConfig.AuditAction;
import sailpoint.object.AuditConfig.AuditAttribute;
import sailpoint.object.AuditConfig.AuditClass;
import sailpoint.object.Bundle;
import sailpoint.object.ClassLists;
import sailpoint.object.Configuration;
import sailpoint.object.Dictionary;
import sailpoint.object.DictionaryTerm;
import sailpoint.object.Filter;
import sailpoint.object.ObjectAttribute;
import sailpoint.object.ObjectConfig;
import sailpoint.object.Profile;
import sailpoint.object.QueryOptions;
import sailpoint.object.RoleIndex;
import sailpoint.object.RoleScorecard;
import sailpoint.object.TaskDefinition;
import sailpoint.object.TaskResult;
import sailpoint.object.TaskSchedule;
import sailpoint.object.UIConfig;
import sailpoint.server.Exporter;
import sailpoint.server.Exporter.Cleaner;
import sailpoint.task.BasePluginTaskExecutor;
import sailpoint.tools.GeneralException;
import sailpoint.tools.Util;
import sailpoint.tools.xml.AbstractXmlObject;
import sailpoint.tools.xml.XMLObjectFactory;
import sailpoint.tools.xml.XMLReferenceResolver;
import sailpoint.tools.Message;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;
import org.xml.sax.InputSource;

import org.xml.sax.SAXException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;
//import org.eclipse.core.resources.IFile;
/**
 * Export XML objects from IdentityIQ
 * The provenance of this code is as follows:
 * The original SailPoint source has been in the public domain for some time
 * Keith Smith has made significant modifications to it including use of the
 * IIQDA Style XPath reverse.target.properties files for reverse tokenization.
 * SailPoint Professional Services obtained these codes from one of my clients
 * and used a significant portion of my changes in constructing the SailPoint
 * version of the ObjectExporter plugin.
 * Keith Smith found significant errors in the plugin and a botched attempt
 * to redesign my reverse tokenization code.  Keith has extensively rewritten
 * the plugin with the correct code and tested it.
 * @author <a href="mailto:keith@mercurycyber.com">Keith Smith</a>
 * @author <a href="mailto:paul.wheeler@sailpoint.com">Paul Wheeler</a>
 */
public class ObjectExporter extends BasePluginTaskExecutor {
  private static final String PLUGIN_NAME = "MCObjectExporterPlugin";
  
  private static Log log = LogFactory.getLog(ObjectExporter.class);

  /**
   * Path that we will output directory structure to
   */
  private static final String ARG_BASE_PATH = "basePath";

  /**
   * Remove IDs and creation/modification timestamps if true
   */
  private static final String ARG_REMOVE_IDS = "removeIDs";

  /**
   * Comma-separated list of classes that we will export (all if blank)
   */
  private static final String ARG_CLASS_NAMES = "classNames";

  /**
   * Only export object if created or modified after this date (all dates if
   * blank)
   */
  private static final String ARG_FROM_DATE = "fromDate";

  /**
   * Target properties file for XPath reverse lookup of tokens that will replace
   * matched text
   */
  private static final String ARG_TARGET_PROPS_FILE = "targetPropsFile";

  /**
   * Target properties file for simple reverse lookup of tokens that will replace
   * matched text
   */
  private static final String ARG_SIMPLE_PROPS_FILE = "simplePropsFile";

  /**
   * Custom naming format for exported file using these tokens: $Class$ =
   * Object Class, $Name$ = Object Name
   */
  private static final String ARG_CUSTOM_NAMING_FORMAT = "namingFormat";

  /**
   * Path of directory containing base XML files used for object comparison
   * when exporting supported object types as merge files
   */
  private static final String ARG_MERGE_COMPARE_DIR_PATH = "mergeCompareDirPath";

  /**
   * If true, enclose Beanshell code in a CDATA section and unescape the code.
   */
  private static final String ARG_ADD_CDATA = "addCData";

  /**
   * Regular expression to filter names of objects we want to export.
   */
  private static final String ARG_REGEX_FILTER = "regexFilter";

  /**
   * If true, strip out metadata that is not usually useful when migrating 
   * between environments, such as TaskDefinition statistics and aggregation 
   * timestamps on Applications.
   */
  private static final String ARG_STRIP_METADATA = "stripMetadata";

  /**
   * If true, strip out the 3 email metadata items from a TaskDefinition
   */
  private static final String ARG_STRIP_TDEMAIL_METADATA = "stringTDEmailMetadata";

  /**
   * If true, do not use an ID/Name map for looking up object names from IDs.
   */
  private static final String NO_ID_NAME_MAP = "noIdNameMap";
  private String _basePath=null;
  private boolean _removeIDs=false;
  private List<String> _classNames = new ArrayList<String>();
  private Date _fromDate=null;
  private String _targetPropsFile=null;
  private String _simplePropsFile=null;
  private String _namingFormat=null;
  /**
   * This is the merge compare path for merge files.  This only applies to the following objects:
   * Configuration
   * UIConfig
   * ObjectConfig (not recommended)
   * AuditConfig
   * Dictionary
   */
  private String _mergeCompareDirPath=null;
  /**
   * This is a folder of files to ignore.  You can put all of the OOTB
   * files into this folder to prevent any OOTB objects from being exported
   * which leads you with only what you have created.
   */
  private String _ignoreDirPath=null;
  /**
   * Normal regex filter for class names.  Examples:
   * XYZ.*       means anything that starts with XYZ.  I recommend using this 
   *             prefix method for any object type where there are OOTB objects
   *             such as Rule and Workflow.  Not needed for object types where
   *             there are no OOTB objects such as Application objects
   * ^(Ident|Bund|Managed).* used with ObjectConfig gets only those you specify
   *                         and are the ones you know you customized.
   *                         This basically means any object that starts with any
   *                         of those strings.  This also works nicely with Configuration objects
   */
  private String _regexFilter=null;
  // If set only bundles that eventually inherit this Bundle
  private String _bundleFilter=null;
  // If set and spelled correctly only does the selected types
  private String _bundleTypeFilter=null;
  // Strip the metadata:
  // From TaskDefinitions, strips the statistics and optionally the email and server names
  // From TaskSchedules, strips the nextActualFireTime and sets the last and next executions to null
  // For Application objects, strips, the acctAggregationStart, acctAggregationEnd, and AD deltaAggregation
  // Also for Application strips any field that starts with a capital letter and has the word Timestamp in it
  // such as lastAggregationTimestamp
  // For Bundles, optionally strips Profiles , RoleIndex and RoleScorecard values
  private boolean _stripMetadata=false;
  // If true please strip the 3 email notification entries from Task Definitions
  private boolean _stripTDEmailMetadata=false;
  // KCS 2023-08-13 Adding in strip role metadata this is RoleScorecard and RoleIndex values
  private boolean _stripRoleMetadata=false;
  // Add CDATA
  private boolean _addCData=false;
  // Dont generate the id name map (default is true)
  private boolean _noIdNameMap=false;
  // Set to true by the terminate() method if someone hits stop
  private boolean terminate = false;
  // KCS 2020-06-18 promoted these to class values
  // This is no longer used
  //private boolean useIIQDAReverseTokenization=true;
  // This is no longer used
  //private boolean useOriginalFilename=false;
  // This is no longer used
  //private boolean useIIQDAFilename=true;
  // This is no longer used
  //private boolean usePrettyFilename=false;
  // If true strip the host value from the Task Definitions
  private boolean stripHostsFromTaskDefinitions=true;
  // If true delete profiles from IT Roles
  private boolean _deleteProfiles=false;
  // This is running on a unix box so use correct folder separators
  private boolean unixOrigin=false;
  // total of all exported objects
  private int totalExported = 0;
  // Listing of object types and counts
  private String exportDetails = null;
  // Just a count of objects exported
  private int classObjectsExported = 0;
  private TaskResult taskResult=null;
  private Map<String, String> simpleTokenMap = new HashMap<String, String>();
  private Map<String, Boolean> simpleTokenIgnoreCaseMap = new HashMap<String, Boolean>();

  Map<String, String> iDNameMap = new HashMap<String, String>();
  @SuppressWarnings({"rawtypes","unchecked"})
  @Override
  public void execute(SailPointContext context, TaskSchedule schedule,
    TaskResult result, Attributes args) throws Exception {
    log.debug("XML-001 Starting XML Object Exporter"); 
    taskResult = result;
    _basePath = args.getString("basePath");
    _removeIDs = args.getBoolean("removeIDs");
    _classNames = args.getStringList("classNames");
    _fromDate = args.getDate("fromDate");
    _targetPropsFile = args.getString("targetPropsFile");
    _simplePropsFile = args.getString("simplePropsFile");
    _namingFormat = args.getString("namingFormat");
    _mergeCompareDirPath = args.getString("mergeCompareDirPath");
    _ignoreDirPath = args.getString("ignoreDirPath");
    _addCData = args.getBoolean("addCData");
    _deleteProfiles = args.getBoolean("stripProfiles");
    _regexFilter = args.getString("regexFilter");
    _bundleFilter = args.getString("bundleFilter");
    _bundleTypeFilter = args.getString("bundleTypeFilter");
    _stripMetadata = args.getBoolean("stripMetadata");
    _stripTDEmailMetadata = args.getBoolean("stripTDEmailMetadata");
    // KCS 2023-08-13 Added strip role metadata
    _stripRoleMetadata = args.getBoolean("stripRoleMetadata");
    _noIdNameMap = args.getBoolean("noIdNameMap");
    String folderSep=File.separator;
    if(folderSep.equals("/")) {
      unixOrigin=true;
    }
    if (log.isDebugEnabled()) {
      log.debug("XML-002 Base path: " + _basePath);
      log.debug("XML-003 Remove IDs: " + _removeIDs);
      log.debug("XML-004 Class names: " + _classNames);
      log.debug("XML-005 Regex filter: " + _regexFilter);
      log.debug("XML-006 Bundle filter: " + _bundleFilter);
      log.debug("XML-007 Bundle type filter: " + _bundleTypeFilter);
      log.debug("XML-008 Strip metadata: " + _stripMetadata);
      log.debug("XML-009 From date: " + _fromDate);
      log.debug("XML-010 Target properties file: " + _targetPropsFile);
      log.debug("XML-010 Simple properties file: " + _simplePropsFile);
      log.debug("XML-011 Naming format: " + _namingFormat);
      log.debug("XML-012 Merge comparison base directory: " + _mergeCompareDirPath);
      log.debug("XML-013 Ignore folder base directory: " + _ignoreDirPath);
      log.debug("XML-014 No ID/Name Map: " + _noIdNameMap);
    }
    String defaultClasses = "Application,AuditConfig,Bundle,Capability,Configuration,CorrelationConfig,Custom,Dictionary,DynamicScope,EmailTemplate,Form,FullTextIndex,GroupFactory,IdentityTrigger,IntegrationConfig,LocalizedAttribute,MessageTemplate,ObjectConfig,PasswordPolicy,Plugin,Policy,QuickLink,QuickLinkOptions,RightConfig,Rule,RuleRegistry,SPRight,ScoreConfig,TaskDefinition,TaskSchedule,UIConfig,Workflow,Workgroup";
    //Map<String, String> tokenMap = new HashMap<>();
    if (!_noIdNameMap) {
      log.debug("XML-015 Building map of IDs to names");
      updateProgress(context, result, "Building id/name map");
      iDNameMap = buildIdNameMap(context);
      if (log.isDebugEnabled()) {
        log.debug("XML-016 Finished building map");
        log.debug("XML-017 Map size: " + iDNameMap.size());
      }
    }
    if (_regexFilter==null) {
      _regexFilter = ".*";
    }
    if (!terminate) {
      //if (_targetPropsFile!=null) {
      //  log.debug("XML-017 loading targetPropsFile: "+_targetPropsFile);
      //  tokenMap = getTokenMap();
      //}
      if (_simplePropsFile!=null) {
        log.debug("XML-017 loading simplePropsFile: "+_simplePropsFile);
        getSimpleTokenMap();
      }
      _basePath = _basePath.replaceAll("\\\\", "/");
      if (!_basePath.endsWith("/")) {
        _basePath = _basePath + "/";
      }
      // KCS 2020-05-08
      if(_basePath.contains("$date$")) {
        DateFormat bpdf=new SimpleDateFormat("yyyyMMdd");
        Date now=new Date();
        String nowStr=bpdf.format(now);
        _basePath=_basePath.replace("$date$", nowStr);
      }
      if(_basePath.contains("$datetime$")) {
        DateFormat bpdf=new SimpleDateFormat("yyyyMMdd-HHmm");
        Date now=new Date();
        String nowStr=bpdf.format(now);
        _basePath=_basePath.replace("$datetime$", nowStr);
      }
      // Check for existence of basePath
      File basePathObj=new File(_basePath);
      if(basePathObj.exists()) {
        log.debug("XML-018 The basePath "+_basePath+" exists");
      }
      else {
        if(basePathObj.mkdirs()) {
          log.debug("XML-019 Successfully created "+_basePath);
        }
        else {
          log.error("XML-020 Count not create folder "+_basePath);
          taskResult.setCompletionStatus(TaskResult.CompletionStatus.Error);
          taskResult.addMessage(new Message(Message.Type.Error,"Could not create output folder"));
          return;
        }
      }
      // Build a map of all the objects we find under the directory containing
      // the comparison files for merges
      Map<String, String> mergeCompareMap = new HashMap<String, String>();
      if ((_mergeCompareDirPath != null) && (!terminate)) {
        _mergeCompareDirPath = _mergeCompareDirPath.replaceAll("\\\\", "/");
        if (!_mergeCompareDirPath.endsWith("/")) {
           _mergeCompareDirPath = _mergeCompareDirPath + "/";
        }
        log.debug("XML-021 Found mergeCompareDirPath="+_mergeCompareDirPath);
        log.debug("XML-022 Obtaining mergeCompareMap");
        mergeCompareMap = getMergeCompareMap();
        for(String mergeKey: mergeCompareMap.keySet()) {
          log.debug("XML-023 mergeCompareMap has key: "+mergeKey);
        }
      }
      //
      // Build a map of ignores
      //
      Map<String, String> ignoreMap = new HashMap<String, String>();
      if ((_ignoreDirPath != null) && (!terminate)) {
        _ignoreDirPath = _ignoreDirPath.replaceAll("\\\\", "/");
        if (!_ignoreDirPath.endsWith("/")) {
           _ignoreDirPath = _ignoreDirPath + "/";
        }
        log.debug("XML-024 Found ignoreDirPath="+_ignoreDirPath);
        log.debug("XML-025 Obtaining ignoreMap");
        ignoreMap = getIgnoreMap();
        for(String ignoreKey: ignoreMap.keySet()) {
          log.debug("XML-026 ignoreMap has key: "+ignoreKey);
        }
      }
      
      // If there's no fromDate assume we want all objects
      if (_fromDate == null) {
        _fromDate = new Date(Long.MIN_VALUE);
      }
      if (_classNames != null && _classNames.size() > 0 && !terminate) {
        log.debug("XML-029 _classNames is populated: "+_classNames.toString());
        if (_classNames.contains("default")) {
          log.debug("XML-029A found default, expanding");
          List<String> defaultClassList = Arrays.asList(defaultClasses.split(","));
          // Use a set to ensure we don't have duplicates if the user has
          // added any default classes to the list
          HashSet<String> mergedClassNames = new HashSet<String>(_classNames);
          mergedClassNames.addAll(defaultClassList);
          _classNames.clear();
          _classNames.addAll(mergedClassNames);
          _classNames.remove("default");
          log.debug("XML-029B _classNames has been repopulated: "+_classNames.toString());
        }
        for (String className : _classNames) {
          if (!terminate) {
            log.debug("XML-029C Exporting class " + className);
            updateProgress(context, result, "Exporting class " + className);
            exportClassObjects(context, className, simpleTokenMap, mergeCompareMap, ignoreMap,
              _regexFilter, _bundleFilter, _bundleTypeFilter);
          }
        }
      }
      else if (!terminate) {
        log.debug("XML-029D class names is left blank.  get them all");
        Class<?>[] allClasses = ClassLists.MajorClasses;
        for (int i = 0; i < allClasses.length; i++) {
          if (!terminate) {
            log.debug("XML-027 processing class "+allClasses[i].getName());
            String className = allClasses[i].getSimpleName();
            log.debug("XML-029E Exporting class " + className);
            updateProgress(context, result, "Exporting class " + className);
            exportClassObjects(context, className, simpleTokenMap, mergeCompareMap, ignoreMap,
              _regexFilter, _bundleFilter, _bundleTypeFilter);
          }
        }
        log.debug("XML-029F Exporting Workgroup objects");
        exportClassObjects(context, "Workgroup", simpleTokenMap, mergeCompareMap, ignoreMap,
          _regexFilter, _bundleFilter, _bundleTypeFilter);
      }
      result.setAttribute("exportDetails", exportDetails);
      result.setAttribute("objectsExported", totalExported);
      log.debug("XML-028 Exiting XML Object Exporter");
    }
    taskResult.setCompletionStatus(TaskResult.CompletionStatus.Success);
    taskResult.addMessage(new Message(Message.Type.Info,"Processed "+totalExported+" objects"));
  }
  /**
   * Export objects of a given class, with reverse-tokenisation using the token
   * map and creating merge files using the merge map.
   */
  @SuppressWarnings("unchecked")  
  private void exportClassObjects(SailPointContext context, String classNameStr, 
    Map<String, String> simpleTokenMap, Map<String, String> mergeCompareMap,
    Map<String, String> ignoreMap,
    String regexFilter, String bundleFilter, String bundleTypeFilter) throws Exception {
    if (log.isDebugEnabled()) {
      log.debug("XML-101 Starting export of class " + classNameStr);
      //log.debug("regexFilter="+regexFilter);
      //log.debug("bundleFilter="+bundleFilter);
      log.debug("XML-102 mergeCompareMap key-value pairs:");
      for(String mergeKey: mergeCompareMap.keySet()) {
        log.debug("XML-103 Key:"+mergeKey+" length:"+mergeCompareMap.get(mergeKey).length());
      }
    }
    String providedClassName = classNameStr;
    if (classNameStr.equalsIgnoreCase("Workgroup")) {
      classNameStr = "Identity"; 
    }
    String fullClassName = "sailpoint.object." + classNameStr;
    Class<? extends SailPointObject> currentClass = null;
    try {
      currentClass = Class.forName(fullClassName).asSubclass(SailPointObject.class);
    }
    catch (ClassNotFoundException e) {
      StringBuffer sb = new StringBuffer();
      sb.append("Could not find class: ");
      sb.append(fullClassName);
      log.warn("XML-104 "+sb.toString());
      taskResult.addMessage(new Message(Message.Type.Warn,"Could not find class: "+fullClassName));
      return;
    } 
    QueryOptions qo = new QueryOptions();
    Filter dateFilter = null;
    if (_fromDate.getTime() != Long.MIN_VALUE) {
      dateFilter = Filter.or(Filter.ge("created", _fromDate), Filter.ge("modified", _fromDate));
      qo.add(dateFilter);
    }
    Filter workgroupFilter = null;
    if (providedClassName.equalsIgnoreCase("Workgroup")) {
      workgroupFilter = Filter.eq("workgroup", true);
      qo.add(workgroupFilter);
    }
    Iterator<Object[]> objIterator = null;
    try {
      objIterator = context.search(currentClass, qo, "id");
    }
    catch (Exception e) {
      if (e.getMessage().contains("could not resolve property:")) { 
        if(dateFilter != null) {
          dateFilter = Filter.ge("created", _fromDate);
          try {
            qo = new QueryOptions();
            qo.add(dateFilter);
            if (workgroupFilter != null) {
              qo.add(workgroupFilter); 
            }
            objIterator = context.search(currentClass, qo, "id");
          }
          catch (Exception e1) {
            if (e1.getMessage().contains("could not resolve property:")) {
               log.warn("XML-105 Ignoring class " + classNameStr + " as it has no modified property");
               taskResult.addMessage(new Message(Message.Type.Warn,"Ignoring class " + classNameStr + " as it has no modified property"));
               return;
            }
          }
        }
      }
      if (e.getMessage().contains("Unsupported filter")) {
        // TaskSchedule objects do not support projection queries, so...
        List<?> objs = context.getObjects(currentClass, qo);
        List<Object[]> ids = new ArrayList<Object[]>();
        if (objs != null && !objs.isEmpty()) {
          for (Object obj : objs) {
            // TaskSchedule objects can include temporary objects for running tasks now.
            // This can include the one for the running Object Exporter task, so ignore these.
            if (classNameStr.equals("TaskSchedule") && "Immediate task runner".equals(((TaskSchedule)obj).getDescription())) {
              continue; 
            }
            String id = ((SailPointObject)obj).getId();
            String[] arrayOfString = new String[1];
            arrayOfString[0] = id;
            ids.add(arrayOfString);
          }
        }
        objIterator = (Iterator<Object[]>) ids.iterator();
      }
    }
    classObjectsExported = 0;
    int counter = 0;
    List<String> propertiesToClean = new ArrayList<String>(Arrays.asList(
      "id", "created", "modified", "targetId", "assignedScopePath",
      "policyId", "assignmentId", "roleId", "identityId", "significantModified"));
    boolean dirCreated = false;
    while (objIterator != null && objIterator.hasNext() && !terminate) {
      Object[] thisObject = objIterator.next();
      String objectId = (String)thisObject[0];
      // Bug found to be modifying the original object, need to just modify a copy.
      SailPointObject objectCopy = (SailPointObject)(context.getObjectById(currentClass, objectId));
      SailPointObject object=(SailPointObject)(objectCopy.deepCopy((Resolver)context));
      //
      // KCS 2022-06-15 Added bundleFilter for CHOA
      //
      boolean skipFile=false;
      if(providedClassName.equalsIgnoreCase("bundle")) {
        boolean foundOuterMatch=false;
        boolean foundTypeMatch=true;
        boolean foundInheritMatch=true;
        if(Util.isNotNullOrEmpty(bundleTypeFilter)) {
          foundTypeMatch=false;
          try {
            Bundle bobj=(Bundle)object;
            String bobjName=bobj.getName();
            String bobjType=bobj.getType();
            log.trace("XML-106 Looking to see if "+bobjName+" is of type "+bundleTypeFilter);
            if(bobjType!=null && !bobjType.isEmpty()) {
              if(Util.nullSafeEq(bobjType.toLowerCase(),bundleTypeFilter.toLowerCase())) {
                log.trace("XML-107 Found type match:"+bobjName);
                foundTypeMatch=true;
              }
            }
            else {
              log.warn("XML-108a Bundle named "+bobjName+" is null or empty, might want to check it.");
            }
          }
          catch (Exception ex) {
            log.error("XML-108 Checking bundle type: "+ex.getClass().getName()+":"+ex.getMessage());
          }
        }
        if(Util.isNotNullOrEmpty(bundleFilter)) {
          foundInheritMatch=false;
          try {
            Bundle bobj=(Bundle)object;
            String bobjName=bobj.getName();
            String bobjType=bobj.getType();
            log.trace("XML-109 Looking to see if "+bobjName+" inherits "+bundleFilter);
            if(Util.nullSafeEq(bobjName,bundleFilter)) {
              log.trace("XML-110 Found exact match:"+bobjName);
              foundInheritMatch=true;
            }
            Collection<Bundle> inherits=bobj.getFlattenedInheritance();
            if(inherits!=null && !inherits.isEmpty()) {
              for (Bundle binh: inherits) {
                String binhName=binh.getName();
                if(Util.nullSafeEq(binhName,bundleFilter)) {
                  log.trace("XML-111 Found inheritance match:"+bobjName);
                  foundInheritMatch=true;
                  break;
                }
              }
            }
          }
          catch (Exception ex) {
            log.error("XML-112 Checking inheritance: "+ex.getClass().getName()+":"+ex.getMessage());
          }
        }
        foundOuterMatch = foundTypeMatch && foundInheritMatch;
        skipFile=!foundOuterMatch;
      }
      if(skipFile) {
        log.debug("XML-190 Skipping file");
        continue;
      }
      String objectName = null;
      // KCS two changes here: there was no need for an if object!=null block
      // if object is null then continue.
      // Second we want to automatically use ID if the object does not have a name
      if (object == null) continue;
      // objectName is name of the object.  Some objects do not have names
      try {
        objectName = object.getName();
        log.trace("XML-113 objectName:"+objectName);
      }
      catch (Exception oex) {
        objectName = null;
        log.trace("XML-114 objectName is null, getting object ID");
      }
      String normalizedObjectName = null;
      if (objectName == null) {
        objectName = objectId;
      }
      log.debug("XML-191 objectName="+objectName+", checking ignoreMap");
      //
      // Here we are going to check the ignoreMap
      //
      String ignoreCheckStr=providedClassName+","+objectName;
      if(ignoreMap.containsKey(ignoreCheckStr)) {
        log.debug("XML-115 Ignoring file "+ignoreCheckStr);
        continue;
      }
      //updateProgress(context, taskResult, "Exporting object " + objectName);
      log.debug("XML-192 objectName="+objectName+", checking pattern matcher");
      Pattern filterPattern = Pattern.compile(regexFilter);
      Matcher filterMatcher = filterPattern.matcher(objectName);
      if (filterMatcher.matches()) {
        log.debug("XML-160 filterMatcher matches "+objectName+" with "+regexFilter);
        String fileName=objectName;
        String iiqDAName = getIIQDAName(providedClassName, objectName);
        String modDAName = getModIIQDAName(providedClassName, objectName);
        log.debug("XML-161 iiqDAName computed as "+iiqDAName);
        normalizedObjectName = objectName.replaceAll("[^a-zA-Z0-9.-]", "_");
        log.debug("XML-162 normalizedObjectName="+normalizedObjectName);
        if (_namingFormat != null) {
          log.debug("XML-163 namingFormat = "+_namingFormat+", computing");
          fileName = _namingFormat;
          fileName = fileName.replaceAll("\\$Name\\$", normalizedObjectName);
          fileName = fileName.replaceAll("\\$Class\\$", providedClassName);
          log.debug("XML-164 after replacing $Name$ and $Class$, name="+fileName);
          fileName = fileName.replaceAll("\\$Default\\$", iiqDAName);
          log.debug("XML-165 after replacing $Default$, name="+fileName);
          fileName = fileName.replaceAll("\\$NewDefault\\$", modDAName);
          log.debug("XML-166 after replacing $NewDefault$, name="+fileName);
          if (!fileName.toLowerCase().endsWith(".xml"))
            fileName = fileName + ".xml";
          log.debug("XML-167 appended .xml to the name");
        }
        else {
          fileName = iiqDAName + ".xml";
          log.debug("XML-168 null input, using iiqDAName of "+fileName);
        }
        log.debug("XML-193 objectName="+objectName+", checking strip metadata");
        if (_stripMetadata) {
          // Remove anything that is not usually useful when migrating between environments
          if (classNameStr.equals("TaskDefinition")) {
            Attributes taskDefAtts = ((TaskDefinition)object).getArguments();
            if (taskDefAtts != null && !taskDefAtts.isEmpty()) {
              for (Iterator<Map.Entry<String, Object>> it = taskDefAtts.entrySet().iterator(); it.hasNext(); ) {
                Map.Entry<String, Object> entry = it.next();
                if (((String)entry.getKey()).startsWith("TaskDefinition.")) {
                  log.debug("XML-180 Found entry: "+(String)entry.getKey()+" removing");
                  it.remove();
                }
                // KCS Added 2020-06-19 the Host name does not get exported.
                // KCS 2024-03-04 Do not remove this if reverse tokenization is being used
                if (stripHostsFromTaskDefinitions && entry.getKey().startsWith("TaskSchedule.host")) {
                  log.debug("XML-181 Found entry: "+(String)entry.getKey()+" removing IF no tokenization");
                  if(Util.isNullOrEmpty(_targetPropsFile)) {
                    it.remove();
                  }
                  else {
                    log.debug("XML-182 targetPropsFile found:"+_targetPropsFile+", to remove use reverse tokenization");
                  }
                }
                // KCS Added 2020-06-19
                // KCS Added 2022-03-08
                if(_stripTDEmailMetadata && entry.getKey().startsWith("taskCompletionEmail")) {
                  it.remove();
                }
              }
            }
          }
          else if (classNameStr.equals("TaskSchedule")) {
            Map<String, Object> taskSchedMap = ((TaskSchedule)object).getArguments();
            if (taskSchedMap != null && !taskSchedMap.isEmpty()) {
              for (Iterator<Map.Entry<String, Object>> it = taskSchedMap.entrySet().iterator(); it.hasNext(); ) {
                Map.Entry<String, Object> entry = it.next();
                if (((String)entry.getKey()).startsWith("TaskSchedule.") || ((String)entry.getKey()).equals("nextActualFireTime")) {
                  it.remove();
                }
              }
              ((TaskSchedule)object).setLastExecution(null);
              ((TaskSchedule)object).setNextExecution(null);
            }
          }
          else if (classNameStr.equals("Application")) {
            Attributes appAtts = ((Application)object).getAttributes();
            if (appAtts != null && !appAtts.isEmpty()) {
              for (Iterator<Map.Entry<String, Object>> it = appAtts.entrySet().iterator(); it.hasNext(); ) {
                Map.Entry<String, Object> entry = it.next();
                if (((String)entry.getKey()).equals("acctAggregationStart") || ((String)entry
                  .getKey()).equals("acctAggregationEnd") || ("sailpoint.connector.ADLDAPConnector"
                  .equals(((Application)object).getConnector()) && ((String)entry.getKey()).equals("deltaAggregation"))) {
                  it.remove();
                }
                // KCS look for Timestamp in a field that starts with a capital letter
                String keyStr=((String)entry.getKey());
                String keyChar1=keyStr.substring(0,1);
                String keyCharUC=keyChar1.toUpperCase();
                if(keyChar1.equals(keyCharUC) && keyStr.contains("Timestamp")) {
                  it.remove();
                }
              }
            }
            ((Application)object).setScorecard(null);
          }
          // KCS 2020-06-19 Adding remove profile function
          else if (classNameStr.equals("Bundle")) {
            log.debug("XML-194 Found Bundle, checking delete profiles");
            if(_deleteProfiles) {
              log.debug("XML-195 removing profiles");
              List<Profile> profilesToRemove=new ArrayList<Profile>();
              List<Profile> bundleProfiles=((Bundle)object).getProfiles();
              for(Profile profToRemove:bundleProfiles) {
                profilesToRemove.add(profToRemove);
              }
              for(Profile profToRemove2:profilesToRemove) {
                ((Bundle)object).remove(profToRemove2);
              }
            }
            log.debug("XML-196 Found Bundle, checking strip role metadata");
            if(_stripRoleMetadata) {
              log.debug("XML-197 removing RoleIndex");
              RoleIndex roleIndex=((Bundle)object).getRoleIndex();
              if(roleIndex!=null) {
                ((Bundle)object).setRoleIndex(null);
              }
              log.debug("XML-198 removing RoleScorecard");
              RoleScorecard roleScorecard=((Bundle)object).getScorecard();
              if(roleScorecard!=null) {
                ((Bundle)object).add(new RoleScorecard());
              }
            }
          }
        }
        String xml = ((AbstractXmlObject)object).toXml();
        log.debug("XML-199 objectName="+objectName+", checking merge options");
        if (_mergeCompareDirPath != null) {
          log.debug("XML-116 Found mergeCompareDirPath");
          if (classNameStr.equals("Configuration")
            || classNameStr.equals("UIConfig")
            || classNameStr.equals("ObjectConfig")
            || classNameStr.equals("AuditConfig")
            || classNameStr.equals("Dictionary")) {
            // SailPoint actually had this still wrong
            log.debug("XML-117 Getting merge compare map entry");
            String origKey = classNameStr + "," + objectName;
            log.debug("XML-118 Entry key = "+origKey);
            String origXml = mergeCompareMap.get(origKey);
            log.debug("XML-119 Got merge compare map");
            if (origXml != null) {
              log.debug("XML-120 origXml length="+origXml.length()+", doing merge");
              XMLObjectFactory f = XMLObjectFactory.getInstance();
              SailPointObject compareObject = (SailPointObject) f.parseXml(context, origXml, true);
              xml = getMergeXml(object, compareObject);
              log.debug("XML-121 Merged xml length="+xml.length());
            }
            else {
              log.debug("XML-122 The origXml value is null, not merging");
            }
          }
          else { 
            log.debug("XML-123 The class is not eligible for merging");
          }
        }
        else {
          log.debug("XML-124 The mergeCompareDirPath is empty");
        }
        log.debug("XML-183 objectName="+objectName+", cleaning the object properties");
        if (_removeIDs) {
          Cleaner cleaner = new Cleaner(propertiesToClean);
          xml = cleaner.clean(xml);
        }
        // Match any 32 character hex id that we can find, unless it's
        // preceded by something
        // that tells us it really needs to be an id, in which case we can't
        // really do anything with it.
        Pattern pattern = Pattern.compile("((?<!Id\" value=\")(?<!id\" value=\")(?<!Id=\")(?<!id=\")(?<!id=)[0-9a-f]{32})");
        Matcher matcher = pattern.matcher(xml);
        while (matcher.find() && !terminate) {
          String id = matcher.group();
          String resolvedObjectName = null;
          if (_noIdNameMap) {
            resolvedObjectName = getObjectNameFromId(context, id);
          } else {
            resolvedObjectName = (String) iDNameMap.get(id);
          }
          if (resolvedObjectName != null) {
            if (log.isDebugEnabled()) {
              log.debug("XML-125 Resolved id " + id + " to " + resolvedObjectName
              + " for object " + objectName + " of class " + classNameStr); 
            }
            xml = xml.replace(id, resolvedObjectName);
          }
        }
        log.debug("XML-184 objectName="+objectName+", checking reverse substitution on "+_targetPropsFile);
        if (_targetPropsFile != null) {
          log.debug("XML-126 xml length before doReverseSubstitution :"+xml.length());
          xml = doReverseSubstitution(xml, _targetPropsFile);
          if(xml==null) {
            log.warn("XML-127 xml returned null from doReverseSubstitution");
            continue;
          }
          else {
            log.debug("XML-128 xml length after doReverseSubstitution :"+xml.length());
            /*
            if(log.isDebugEnabled()) {
              log.debug("XML-128X xml="+xml);
            }
            byte[] crlfcrlf=new byte[]{ (byte)0x0d, (byte)0x0a, (byte)0x0d, (byte)0x0a };
            byte[] crlf=new byte[]{ (byte)0x0d, (byte)0x0a };
            xml=xml.replace(new String(crlfcrlf),new String(crlf));
            log.debug("XML-128A xml length after doReverseSubstitution :"+xml.length());
            byte[] crcr=new byte[]{ (byte)0x0d, (byte)0x0d };
            byte[] cr=new byte[]{ (byte)0x0d };
            xml=xml.replace(new String(crcr),new String(cr));
            log.debug("XML-128B xml length after doReverseSubstitution :"+xml.length());
            byte[] lflf=new byte[]{ (byte)0x0a, (byte)0x0a };
            byte[] lf=new byte[]{ (byte)0x0a };
            xml=xml.replace(new String(lflf),new String(lf));
            log.debug("XML-128C xml length after doReverseSubstitution :"+xml.length());
            */
          }
        }
        log.debug("XML-186 objectName="+objectName+", checking reverse substitution on "+simpleTokenMap.toString());
        if (!simpleTokenMap.isEmpty()) {
          log.debug("XML-151 processing simple reverse tokenization");
          Iterator<Map.Entry<String, String>> it = simpleTokenMap.entrySet().iterator();
          while (it.hasNext() && !terminate) {
            Map.Entry<String, String> pairs = it.next();
            String token = pairs.getKey();
            Boolean ignoreCase=simpleTokenIgnoreCaseMap.get(token);
            String value = pairs.getValue();
            if(value.startsWith("%%")) {
              String x=value;
              value=token;
              token=x;
            }
            log.debug("XML-152 processing ("+token+","+value+")");
            String containsValue = value.replace("\\\\", "\\");
            if (log.isDebugEnabled()) {
              log.debug("XML-129 Checking for token value " + value);
            }
            if(ignoreCase.booleanValue()) {
              log.debug("XML-331 ignoreCase found to be true, using case insensitive logic");
              if ((xml.toLowerCase()).contains(containsValue.toLowerCase())) {
                log.debug("XML-332 found a case insensitive match");
                String replaceValue = value.replaceAll("\\\\", "\\\\");
                replaceValue = replaceValue.replaceAll("\\+", "\\\\+");
                replaceValue = replaceValue.replaceAll("\\^", "\\\\^");
                replaceValue = replaceValue.replaceAll("\\$", "\\\\" + 
                    Matcher.quoteReplacement("$"));
                replaceValue = replaceValue.replaceAll("\\.", "\\\\.");
                replaceValue = replaceValue.replaceAll("\\|", "\\\\|");
                replaceValue = replaceValue.replaceAll("\\?", "\\\\?");
                replaceValue = replaceValue.replaceAll("\\*", "\\\\*");
                replaceValue = replaceValue.replaceAll("\\(", "\\\\(");
                replaceValue = replaceValue.replaceAll("\\)", "\\\\)");
                replaceValue = replaceValue.replaceAll("\\[", "\\\\[");
                replaceValue = replaceValue.replaceAll("\\{", "\\\\{");
                if (log.isDebugEnabled()) {
                  log.debug("XML-330 Found value " + replaceValue + ", replacing with token " + token);
                }
                xml=combAllCasePatterns(replaceValue, token, xml);
              }
            }
            else {
              if (xml.contains(containsValue)) {
                String replaceValue = value.replaceAll("\\\\", "\\\\");
                replaceValue = replaceValue.replaceAll("\\+", "\\\\+");
                replaceValue = replaceValue.replaceAll("\\^", "\\\\^");
                replaceValue = replaceValue.replaceAll("\\$", "\\\\" + 
                    Matcher.quoteReplacement("$"));
                replaceValue = replaceValue.replaceAll("\\.", "\\\\.");
                replaceValue = replaceValue.replaceAll("\\|", "\\\\|");
                replaceValue = replaceValue.replaceAll("\\?", "\\\\?");
                replaceValue = replaceValue.replaceAll("\\*", "\\\\*");
                replaceValue = replaceValue.replaceAll("\\(", "\\\\(");
                replaceValue = replaceValue.replaceAll("\\)", "\\\\)");
                replaceValue = replaceValue.replaceAll("\\[", "\\\\[");
                replaceValue = replaceValue.replaceAll("\\{", "\\\\{");
                if (log.isDebugEnabled()) {
                  log.debug("XML-130 Found value " + replaceValue + ", replacing with token " + token); 
                }
                xml = xml.replaceAll(replaceValue, token);
              }
            }
          }
        }
        else {
          log.debug("XML-131 simpleTokenMap is empty");
        }
        log.debug("XML-132 xml length before replace:"+xml.length());
        int beforeLen=xml.length();
        int afterLen=0;
        String checkfor="\r\n";
        if(unixOrigin) {
          checkfor="\n";
        }
        while(beforeLen > afterLen) {
          beforeLen=xml.length();
          xml = xml.replace("        "+checkfor,checkfor);
          xml = xml.replace("    "+checkfor,checkfor);
          xml = xml.replace("  "+checkfor,checkfor);
          xml = xml.replace(" "+checkfor,checkfor);
          afterLen=xml.length();
        }
        xml = xml.replace(checkfor+checkfor, checkfor);
        xml = xml.replace(checkfor+checkfor, checkfor);
        log.debug("XML-133 xml length before addCData() :"+xml.length());
        if (_addCData) {
          xml = addCData(normalizedObjectName,xml);
        }
        //xml = xml.replaceAll("\\n", "\r\n");
        if (!dirCreated) {
          File dir = new File(_basePath + providedClassName);
          if (!dir.exists()) {
            if (dir.mkdirs()) {
              dirCreated = true;
              if (log.isDebugEnabled()) {
                log.debug("XML-134 Created directory " + dir.getPath()); 
              }
            }
            else {
              log.error("XML-135 Could not create directory " + dir.getPath() + "!");
            }
          }
          else {
            dirCreated = true;
            if (log.isDebugEnabled()) {
              log.debug("XML-136 Directory " + dir.getPath() + " already exists");
            }
          }
        }
        if (log.isDebugEnabled()) {
          log.debug("XML-137 Exporting " + providedClassName + " " + objectName + " to " + _basePath + providedClassName + "/" + fileName); 
        }
        // KCS Edits to change the single quotes to double quotes
        String badStart="<?xml version='1.0' encoding='UTF-8'?>";
        String goodStart="<?xml version=\"1.0\" encoding=\"UTF-8\"?>";
        if(xml.startsWith(badStart)) {
          xml=goodStart+xml.substring(badStart.length());
        }
        // Trying here to add CRs to the Description tags
        //xml=xml.replace("<Description>","<Description>\n");
        //xml=xml.replace("</Description>","\n</Description");
        if(xml.contains("<Description>")) {
          int xmllen=xml.length();
          // Until you reach the end, fix the descriptions
          int dindex=0;
          int eindex=0;
          do {
            // dindex is the next location of a description tag after the last one
            dindex=xml.indexOf("<Description>",eindex);
            if(dindex > 0) {
              log.debug("XML-138 Found an instance of <Description> at location "+dindex); 
              // This was written with lastIndexOf but seems it should just be indexOf
              int crindex=xml.lastIndexOf("\n",dindex);
              int numspaces=dindex-crindex;
              log.debug("XML-139 Backwards search for CR found an instance at "+crindex+" num spaces="+numspaces); 
              eindex=xml.indexOf("</Description>",dindex);
              if(eindex<0) {
                log.warn("XML-140 Did not find a Description end tag");
                eindex=dindex+13;
              }
              else {
                log.debug("XML-141 Found the end tag </Description> at location "+eindex); 
                //
                // Check to see if this already has carriage returns
                //
                boolean alreadyFixed=false;
                if('\n'==(xml.charAt(dindex+1))) {
                  alreadyFixed=true;
                }
                if(!alreadyFixed) {
                  int totallength=eindex-dindex;
                  if(totallength > 53) {
                    StringBuffer sb1=new StringBuffer();
                    sb1.append(xml.substring(0,(dindex+13)));
                    sb1.append("\n");
                    for(int ispc=0; ispc<(numspaces+1); ispc++) {
                      sb1.append(" ");
                    }
                    sb1.append( (xml.substring((dindex+13),eindex)).trim());
                    sb1.append("\n");
                    for(int ispc=0; ispc<(numspaces-1); ispc++) {
                      sb1.append(" ");
                    }
                    sb1.append(xml.substring(eindex));
                    xml=sb1.toString();
                  }
                }
              }
            }
          } while (dindex > 0);
        }
        xml=xml.replace("<Description/>","<Description></Description>");
        xml=xml.replace("<Boolean/>","<Boolean></Boolean>");
        // KCS End of Edits, added trailing cr to end in order to match IIQDA
        if(xml.endsWith("\n")) {
          log.debug("XML-142 File already ends with cr");
        }
        else {
          log.debug("XML-143 Adding cr to end of file");
          xml=xml+"\n";
        }
        Util.writeFile(_basePath + providedClassName + "/" + fileName, xml);
        totalExported++;
        classObjectsExported++;
        counter++;
        if (counter > 49) {
          context.decache();
          counter = 0;
        }
      }
      else {
        log.debug("XML-187 no match to the pattern match");
      }
    }
    Util.flushIterator(objIterator);
    if (classObjectsExported > 0) {
      if (exportDetails == null) {
        exportDetails = providedClassName + ": " + classObjectsExported;
      }
      else {
        exportDetails += ", " + providedClassName + ": " + classObjectsExported;
      }
    }
  }
  /**
   * Comb through to see if there is a match
   */
  private String combAllCasePatterns(String wordIn, String token, String replaceIn) {
    log.debug("XML-400 Trying "+wordIn+" on "+replaceIn);
    String replaceOut=replaceIn;
    String word=wordIn;
    int wordlen=word.length();
    log.debug("XML-401 word length is "+wordlen);
    byte[] wordchars=word.getBytes(StandardCharsets.UTF_8);
    byte[] packedchars=new byte[wordlen];
    boolean[] isalphachar=new boolean[wordlen];
    int packedlen=0;
    for(int ipack=0; ipack<wordlen; ++ipack) {
      byte chb=wordchars[ipack];
      if((chb>=65 && chb<=90) || (chb>=97 && chb<=122)) {
        packedchars[packedlen]=chb;
        isalphachar[ipack]=true;
        packedlen++;
      }
      else {
        isalphachar[ipack]=false;
      }
    }
    byte[] newpack=new byte[packedlen];
    for(int ipack=0; ipack<packedlen; ++ipack) {
      newpack[ipack]=packedchars[ipack];
    }
    word = new String(newpack, StandardCharsets.US_ASCII);
    log.debug("XML-402 word length after removing non-letters:"+packedlen);
    log.debug("XML-403 word after removing non-letters:"+word);
    word = word.toLowerCase();
    long combinations = 1L << word.length();
    for (long i = 0L; i < combinations; i++) {
      char[] result = word.toCharArray();
      for (int j = 0; j < word.length(); j++) {
        if (((i >> j) & 1) == 1 ) {
          result[j] = Character.toUpperCase(word.charAt(j));
        }
      }
      log.debug("XML-404 Trying combination "+i+" of "+combinations
        +" :"+new String(result));
      // Rebuild the word from the packed characters
      packedlen=0;
      for(int ipack=0; ipack<wordlen; ++ipack) {
        if(isalphachar[ipack]) {
          packedchars[ipack]=(byte)(result[packedlen]);
          packedlen++;
        }
        else {
          packedchars[ipack]=wordchars[ipack];
        }
      }
      log.debug("XML-405 Trying combination "+i+" of "+combinations
        +" :"+new String(packedchars,StandardCharsets.US_ASCII));
      replaceOut=replaceIn.replace(new String(packedchars,StandardCharsets.US_ASCII), token);
      // Stop on any replace
      if(!replaceOut.equals(replaceIn)) return replaceOut;
    }
    return replaceOut;
  }
  /**
   * Return the name of an object from a given ID, where we don't know the
   * class.
   */
  @SuppressWarnings("unchecked")
  private String getObjectNameFromId(SailPointContext context, String id) throws GeneralException {
    String resolvedObjectName = id;
    SailPointObject object = null;
    for (Class<SailPointObject> cls : ClassLists.MajorClasses) {
      if (!terminate) {
        try {
          object = context.getObjectById(cls, id);
        }
        catch(Exception ex) {
          log.error("XML-406 Issue with class: "+ex.getClass().getName()+":"+ex.getMessage());
        }
        if (object != null) {
          break;
    }
      } 
    } 
    if (object == null) {
      return null;
    }
    try {
      resolvedObjectName = object.getName();
    }
    catch (Exception e) {
      if (e.getMessage().contains("Could not resolve property:")) {
        log.debug("XML-150 Ignoring class " + object.getClass().getName() + " as it has no name property"); 
      }
    }
    return resolvedObjectName;
  }
   /**
    * Get the tokens and their values from the referenced target properties file
    * and build a map that we can use for reverse-tokenisation.
    * KCS 2019-02-19 this is deprecated the reverse tokenization file doesn't use this
    * KCS - SailPoint screwed this up using NIO it doesn't close the file
    
  @SuppressWarnings("unchecked")
  private Map<String, String> getTokenMap() throws GeneralException, IOException {
    Map<String, String> tokenMapFromPropsFile = new HashMap<>();
    BufferedReader br = new BufferedReader(new FileReader(_targetPropsFile));
    log.debug("XML-201 Entered getTokenMap");
    try {
      String line = br.readLine();
      while(line != null && !terminate) {
        if (line.startsWith("%%") && line.contains("=") && !line.contains("%%TARGET%%")) {
          String[] splitLine = line.split("=", 2);
          String tokenName = splitLine[0];
          String tokenValue = splitLine[1];
          // Ignore simple true/false values - these will not be tokenised
           * as they appear everywhere.
           * Also ignore any value that is just whitespace or blank.
           //
          if (!tokenValue.toLowerCase().equals("true") && 
            !tokenValue.toLowerCase().equals("false") && tokenValue
            .trim().length() > 0)
            tokenMapFromPropsFile.put(tokenName, tokenValue); 
        }
        line = br.readLine();
      }
    }
    catch (Exception ex) {
      log.error("XML-202 Error in getTokenMap:"+ex.getClass().getName()+":"+ex.getMessage());
    }
    finally {
      br.close();
    }
    return tokenMapFromPropsFile;
  }
  */
   /**
    * Get the tokens and their values from the referenced target properties file
    * and build a map that we can use for reverse-tokenisation.
    * KCS 2023-09-19 get the simple token map
    */
  @SuppressWarnings("unchecked")
  private void getSimpleTokenMap() throws GeneralException, IOException {
    BufferedReader br = new BufferedReader(new FileReader(_simplePropsFile));
    log.debug("XML-201 Entered getSimpleTokenMap");
    try {
      String line = br.readLine();
      while(line != null && !terminate) {
        /*
         *   KCS 10-13-2023 this original method is not correct. It prevents multiple
         *                  values from being tokenized to the same value. I am going
         *                  to leave it in case someone wants to use this method
         *                  but the correct method is below.
         */
        if (line.startsWith("%%") && line.contains("=") && !line.contains("%%TARGET%%")) {
          String[] splitLine = line.split("=", 2);
          String tokenName = splitLine[0];
          String tokenValue = splitLine[1];
          log.debug("XML-202 Found old style mapping: "+tokenName+"="+tokenValue+"  << Saving to map");
          /* Ignore simple true/false values - these will not be tokenised
           * as they appear everywhere.
           * Also ignore any value that is just whitespace or blank.
           */
          if (!tokenValue.toLowerCase().equals("true") && 
            !tokenValue.toLowerCase().equals("false") && tokenValue
            .trim().length() > 0) {
            simpleTokenMap.put(tokenName, tokenValue);
            simpleTokenIgnoreCaseMap.put(tokenName, Boolean.valueOf(false));
          }
        }
        else if(line.endsWith("%%") && line.contains("=") && !line.contains("%%TARGET%%")) {
          // Here we have to pull the last = sign out and what is to the left of that is
          // token value and what is to the right is the token name
          int lastEqual=line.lastIndexOf("=");
          String tokenName=line.substring(lastEqual+1);
          String tokenValue=line.substring(0,lastEqual);
          log.debug("XML-203 Found new style mapping: "+tokenValue+"="+tokenName+"  << Saving to map");
          if (!tokenValue.toLowerCase().equals("true") && 
            !tokenValue.toLowerCase().equals("false") && tokenValue
            .trim().length() > 0) {
            if(tokenName.endsWith("%%%")) {
              tokenName=tokenName.substring(0,tokenName.length()-1);
              simpleTokenIgnoreCaseMap.put(tokenValue, Boolean.valueOf(true));
              log.debug("XML-204 found ignore case token fixing to "+tokenName);
            }
            else {
              simpleTokenIgnoreCaseMap.put(tokenValue, Boolean.valueOf(false));
              log.debug("XML-205 found normal token "+tokenName);
            }
            simpleTokenMap.put(tokenValue, tokenName);
          }
        }
        line = br.readLine();
      }
    }
    catch (Exception ex) {
      log.error("XML-202 Error in getTokenMap:"+ex.getClass().getName()+":"+ex.getMessage());
    }
    finally {
      br.close();
    }
  }
  
  @SuppressWarnings("unchecked")
  private Map<String, String> getMergeCompareMap() throws GeneralException, IOException {
    log.debug("XML-210 Entered getMergeCompareMap, creating new HashMap");
    Map<String, String> mergeMap = new HashMap<String,String>();
    File dir = new File(_mergeCompareDirPath);
    if (!dir.exists()) {
      throw new GeneralException("Merge comparison path " + dir.toString() + " does not exist"); 
    }
    List<String> compareFiles = listXmlFilesForDir(dir);
    for (String compareFile : compareFiles) {
      if (!terminate) {
        log.debug("XML-211 Reading " + compareFile);
        String origXml = null;
        BufferedReader br = new BufferedReader(new FileReader(compareFile));
        StringBuilder origXmlSB = new StringBuilder();
        try {
          String line = br.readLine();
          while(line!=null && !terminate) {
            if (origXml != null) {
              origXmlSB.append("\n" + line);
              line = br.readLine();
            }
            else {
              origXmlSB.append(line);
              line = br.readLine();
            }
          }
          origXml = origXmlSB.toString();
          log.debug("XML-213 read file in, length="+origXml.length());
          String xmlClassName = null;
          String xmlObjectName = null;
          Pattern classPattern = Pattern.compile("!DOCTYPE (.*?) PUBLIC");
          Matcher classMatcher = classPattern.matcher(origXml);
          if (classMatcher.find()) {
            xmlClassName = classMatcher.group(1).trim();
          }
          log.debug("XML-214 class name = "+xmlClassName);
          Pattern namePattern = Pattern.compile("name=\"(.*?)\"");
          Matcher nameMatcher = namePattern.matcher(origXml);
          if (nameMatcher.find()) {
            xmlObjectName = nameMatcher.group(1).trim();
          }
          if (xmlClassName != null && xmlObjectName != null) {
            String objectKey = xmlClassName + "," + xmlObjectName;
            log.debug("XML-215 Adding " + objectKey + " ("+origXml.length()+" bytes)");
            mergeMap.put(objectKey, origXml);
          }
        }
        catch (Exception ex) {
          log.error("XML-216 Error in getMergeCompareMap:"+ex.getClass().getName()+":"+ex.getMessage());
        }
        finally {
          br.close();
        }
      }
    } 
    return mergeMap;
  }
  /**
   * getIgnoreMap reads in the files from the ignoreDirPath and sorts out the
   * class names and object names for filtering out
   */
  @SuppressWarnings("unchecked")
  private Map<String, String> getIgnoreMap() throws GeneralException, IOException {
    log.debug("XML-221 Entered getIgnoreMap, creating new HashMap");
    Map<String, String> ignoreMap = new HashMap<String,String>();
    File dir = new File(_ignoreDirPath);
    if (!dir.exists()) {
      throw new GeneralException("Ignore path " + dir.toString() + " does not exist"); 
    }
    List<String> ignoreFiles = listXmlFilesForDir(dir);
    for (String ignoreFile : ignoreFiles) {
      if (!terminate) {
        log.debug("XML-222 Reading " + ignoreFile);
        String origXml = null;
        BufferedReader br = new BufferedReader(new FileReader(ignoreFile));
        StringBuilder origXmlSB = new StringBuilder();
        try {
          String line = br.readLine();
          while(line!=null && !terminate) {
            if (origXml != null) {
              origXmlSB.append("\n" + line);
              line = br.readLine();
            }
            else {
              origXmlSB.append(line);
              line = br.readLine();
            }
          }
          origXml = origXmlSB.toString();
          log.debug("XML-223 read file in, length="+origXml.length());
          /*
           * Initialize the Class Name and Object Name
           */
          String xmlClassName = null;
          String xmlObjectName = null;
          /*
           * Find the class name
           */
          Pattern classPattern = Pattern.compile("!DOCTYPE (.*?) PUBLIC");
          Matcher classMatcher = classPattern.matcher(origXml);
          if (classMatcher.find()) {
            xmlClassName = classMatcher.group(1).trim();
          }
          log.debug("XML-224 class name = "+xmlClassName);
          /*
           * Find the object name
           */
          Pattern namePattern = Pattern.compile("name=\"(.*?)\"");
          Matcher nameMatcher = namePattern.matcher(origXml);
          if (nameMatcher.find()) {
            xmlObjectName = nameMatcher.group(1).trim();
          }
          /*
           * Added by Keith Smith 2024-02-28 for version 1.0.2
           */
          if("Identity".equals(xmlClassName)) {
            // Let us see if this is a Workgroup
            Pattern wgPattern = Pattern.compile("workgroup=\"(.*?)\"");
            Matcher wgMatcher = wgPattern.matcher(origXml);
            if (wgMatcher.find()) {
              String wgValue = wgMatcher.group(1).trim();
              if("true".equals(wgValue)) {
                log.debug("XML-227 object "+xmlObjectName+"is a Workgroup");
                xmlClassName="Workgroup";
              }
            }
          }
          /*
           * Sum up and save to ignore map
           */
          if (xmlClassName != null && xmlObjectName != null) {
            String objectKey = xmlClassName + "," + xmlObjectName;
            log.debug("XML-225 Adding " + objectKey + " ("+origXml.length()+" bytes)");
            ignoreMap.put(objectKey, origXml);
          }
        }
        catch (Exception ex) {
          log.error("XML-226 Error in getIgnoreMap:"+ex.getClass().getName()+":"+ex.getMessage());
        }
        finally {
          br.close();
        }
      }
    } 
    return ignoreMap;
  }

  @SuppressWarnings("unchecked")
  private Map<String, String> buildIdNameMap(SailPointContext context) throws GeneralException {
    log.debug("XML-230 Entered buildIdNameMap");
    Map<String, String> iDNameMap = new HashMap<>();
    Class<?>[] allMajorClasses = ClassLists.MajorClasses;
    for (int i = 0; i < allMajorClasses.length; i++) {
      if (!terminate) {
        String classNameStr = allMajorClasses[i].getSimpleName();
        String fullClassName = "sailpoint.object." + classNameStr;
        Class<? extends SailPointObject> currentClass = null;
        try {
          currentClass = Class.forName(fullClassName).asSubclass(SailPointObject.class);
        } catch (Exception e) {
          StringBuffer sb = new StringBuffer();
          sb.append("Could not find class: ");
          sb.append(fullClassName);
          throw new GeneralException(sb.toString());
        } 
        try {
          log.debug("XML-231 Adding to ID/Name map for class " + classNameStr); 
          QueryOptions qo = new QueryOptions();
          if (classNameStr.equals("Identity")) {
            List<Boolean> trueAndFalse = new ArrayList<>();
            trueAndFalse.add(Boolean.TRUE);
            trueAndFalse.add(Boolean.FALSE);
            qo.addFilter(Filter.in("workgroup", trueAndFalse));
          } 
          Iterator<Object[]> it = context.search(currentClass, qo, "name, id");
          while (it.hasNext() && !terminate) {
            Object[] obj = it.next();
            String objName = (String)obj[0];
            if (objName != null) {
              String objId = (String)obj[1];
              log.trace("XML-232 Adding " + objId + " " + objName);
              iDNameMap.put(objId, objName);
            } 
          } 
          Util.flushIterator(it);
        } catch (Exception e) {
          if (e.getMessage().contains("could not resolve property:")) {
            log.debug("XML-233 Ignoring class " + classNameStr + " as it has no name property");
          }
        }
      }
    }
    return iDNameMap;
  }
  
  @SuppressWarnings("unchecked")
  private List<String> listXmlFilesForDir(File dir) {
    log.debug("XML-240 Entered listXmlFilesForDir "+dir.getAbsolutePath());
    List<String> fileList = new ArrayList<>();
    for (File fileEntry : dir.listFiles()) {
      if (fileEntry.isDirectory()) {
         log.debug("XML-241 found a directory: "+fileEntry.getAbsolutePath());
        fileList.addAll(listXmlFilesForDir(fileEntry));
      }
      else {
        String filePath = fileEntry.getPath();
        if (filePath.toLowerCase().endsWith(".xml")) {
          fileList.add(filePath);
          log.debug("XML-242 Found file path: " + filePath);
        }
      }
    }
    log.debug("XML-243 returning fileList of length "+fileList.size());
    return fileList;
  }
  /**
   * merge the result into the old result
   */
  @SuppressWarnings("unchecked")
  private String getMergeXml(SailPointObject object, SailPointObject compareObject) throws GeneralException, NoSuchMethodException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, InstantiationException {
    /*
     *  4/30/2023 Apparently whoever wrote this did not care to do any logging or comments
     *  Since that is the case and it's broken no one can complain if I fix it.
     *  compareObject is the XML that's in the file
     *  Class<? extends SailPointObject> is a class model
     *  Method is a java.lang.reflect.Method
     */
    String mergeXml = null;
    Class<? extends SailPointObject> clazz = (Class)compareObject.getClass();
    log.debug("XML-250 In getMergeXml for class "+clazz.getName());
    
    log.debug("XML-251 Creating casts of the inputs.");
    SailPointObject baseObject = clazz.cast(compareObject);
    SailPointObject currentObject = clazz.cast(object);
    
    log.debug("XML-252 Creating empty Attributes objects");
    Attributes baseAttributes = new Attributes();
    Attributes currentAttributes = new Attributes();
    
    log.debug("XML-253 Creating empty List<ObjectAttribute> lists");
    List<ObjectAttribute> baseObjectAttributes = new ArrayList<ObjectAttribute>();
    List<ObjectAttribute> currentObjectAttributes = new ArrayList<ObjectAttribute>();
    
    log.debug("XML-254 Creating empty Map<String, ObjectAttribute> maps");
    Map<String, ObjectAttribute> baseObjectAttributesMap = new HashMap<String, ObjectAttribute>();
    Map<String, ObjectAttribute> currentObjectAttributesMap = new HashMap<String, ObjectAttribute>();
    
    log.debug("XML-255 Creating empty List<AuditConfig.AuditAttribute> lists");
    List<AuditConfig.AuditAttribute> baseAuditAttributes = new ArrayList<AuditConfig.AuditAttribute>();
    List<AuditConfig.AuditAttribute> currentAuditAttributes = new ArrayList<AuditConfig.AuditAttribute>();
    
    log.debug("XML-256 Creating empty Map<String, AuditConfig.AuditAttribute> maps");
    Map<String, AuditConfig.AuditAttribute> baseAuditAttributesMap = new HashMap<String, AuditConfig.AuditAttribute>();
    Map<String, AuditConfig.AuditAttribute> currentAuditAttributesMap = new HashMap<String, AuditConfig.AuditAttribute>();
    
    log.debug("XML-257 Creating empty List<AuditConfig.AuditClass> lists");
    List<AuditConfig.AuditClass> baseAuditClasses = new ArrayList<AuditConfig.AuditClass>();
    List<AuditConfig.AuditClass> currentAuditClasses = new ArrayList<AuditConfig.AuditClass>();
    
    log.debug("XML-258 Creating empty Map<String, AuditConfig.AuditClass> maps");
    Map<String, AuditConfig.AuditClass> baseAuditClassesMap = new HashMap<String, AuditConfig.AuditClass>();
    Map<String, AuditConfig.AuditClass> currentAuditClassesMap = new HashMap<String, AuditConfig.AuditClass>();
    
    log.debug("XML-259 Creating empty List<AuditConfig.AuditAction> lists");
    List<AuditConfig.AuditAction> baseAuditActions = new ArrayList<AuditConfig.AuditAction>();
    List<AuditConfig.AuditAction> currentAuditActions = new ArrayList<AuditConfig.AuditAction>();
    
    log.debug("XML-260 Creating empty Map<String, AuditConfig.AuditAction> maps");
    Map<String, AuditConfig.AuditAction> baseAuditActionsMap = new HashMap<String, AuditConfig.AuditAction>();
    Map<String, AuditConfig.AuditAction> currentAuditActionsMap = new HashMap<String, AuditConfig.AuditAction>();
    
    log.debug("XML-261 Creating empty List<DictionaryTerm> lists");
    List<DictionaryTerm> baseDictionaryTerms = new ArrayList<DictionaryTerm>();
    List<DictionaryTerm> currentDictionaryTerms = new ArrayList<DictionaryTerm>();
    
    log.debug("XML-262 Creating empty List<String> dictionary lists");
    List<String> baseDictionaryTermsValues = new ArrayList<String>();
    List<String> currentDictionaryTermsValues = new ArrayList<String>();
    
    if (compareObject instanceof sailpoint.object.Configuration || compareObject instanceof sailpoint.object.UIConfig) {
      log.debug("XML-263 Found a Configuration or UIConfig object, just processing attributes");
      Method getAttributesMethod = clazz.getMethod("getAttributes", (Class[])null);
      baseAttributes = (Attributes)getAttributesMethod.invoke(baseObject, (Object[])null);
      currentAttributes = (Attributes)getAttributesMethod.invoke(currentObject, (Object[])null);
    } 
    else if (compareObject instanceof sailpoint.object.ObjectConfig) {
      log.debug("XML-264 Found an ObjectConfig object, processing attributes and objectAttributes");
      Method getConfigAttributesMethod = clazz.getMethod("getConfigAttributes", (Class[])null);
      baseAttributes = (Attributes)getConfigAttributesMethod.invoke(baseObject, (Object[])null);
      currentAttributes = (Attributes)getConfigAttributesMethod.invoke(currentObject, (Object[])null);
      Method getObjectAttributesMethod = clazz.getMethod("getObjectAttributes", (Class[])null);
      baseObjectAttributes = (List<ObjectAttribute>)getObjectAttributesMethod.invoke(baseObject, (Object[])null);
      if (baseObjectAttributes != null) {
        for (ObjectAttribute baseObjectAttribute : baseObjectAttributes) {
          baseObjectAttributesMap.put(baseObjectAttribute.getName(), baseObjectAttribute);
        }
      }
      currentObjectAttributes = (List<ObjectAttribute>)getObjectAttributesMethod.invoke(currentObject, (Object[])null);
      if (currentObjectAttributes != null) {
        for (ObjectAttribute currentObjectAttribute : currentObjectAttributes) {
          currentObjectAttributesMap.put(currentObjectAttribute.getName(), currentObjectAttribute);
        }
      }
    } 
    else if (compareObject instanceof AuditConfig) {
      log.debug("XML-265 Found an AuditConfig object, processing attributes and audit attributes");
      Method getAttributesMethod = clazz.getMethod("getAttributes", (Class[])null);
      baseAuditAttributes = (List<AuditConfig.AuditAttribute>)getAttributesMethod.invoke(baseObject, (Object[])null);
      if (baseAuditAttributes != null) {
        for (AuditConfig.AuditAttribute baseAuditAttribute : baseAuditAttributes) {
          baseAuditAttributesMap.put(baseAuditAttribute.getName(), baseAuditAttribute);
        }
      }
      currentAuditAttributes = (List<AuditConfig.AuditAttribute>)getAttributesMethod.invoke(currentObject, (Object[])null);
      if (currentAuditAttributes != null) {
        for (AuditConfig.AuditAttribute currentAuditAttribute : currentAuditAttributes) {
          currentAuditAttributesMap.put(currentAuditAttribute.getName(), currentAuditAttribute);
        }
      }
      Method getClassesMethod = clazz.getMethod("getClasses", (Class[])null);
      baseAuditClasses = (List<AuditConfig.AuditClass>)getClassesMethod.invoke(baseObject, (Object[])null);
      if (baseAuditClasses != null) {
        for (AuditConfig.AuditClass baseAuditClass : baseAuditClasses) {
          baseAuditClassesMap.put(baseAuditClass.getName(), baseAuditClass);
        }
      }
      currentAuditClasses = (List<AuditConfig.AuditClass>)getClassesMethod.invoke(currentObject, (Object[])null);
      if (currentAuditClasses != null) {
        for (AuditConfig.AuditClass currentAuditClass : currentAuditClasses) {
          currentAuditClassesMap.put(currentAuditClass.getName(), currentAuditClass);
        }
      }
      Method getActionsMethod = clazz.getMethod("getActions", (Class[])null);
      baseAuditActions = (List<AuditConfig.AuditAction>)getActionsMethod.invoke(baseObject, (Object[])null);
      if (baseAuditActions != null) {
        for (AuditConfig.AuditAction baseAuditAction : baseAuditActions)  {
          baseAuditActionsMap.put(baseAuditAction.getName(), baseAuditAction);
        }
      }
      currentAuditActions = (List<AuditConfig.AuditAction>)getActionsMethod.invoke(currentObject, (Object[])null);
      if (currentAuditActions != null) {
        for (AuditConfig.AuditAction currentAuditAction : currentAuditActions) {
          currentAuditActionsMap.put(currentAuditAction.getName(), currentAuditAction);
        }
      }
    }
    else if (compareObject instanceof sailpoint.object.Dictionary) {
      log.debug("XML-266 Found an Dictionary object, processing terms");
      Method getTermsMethod = clazz.getMethod("getTerms", (Class[])null);
      baseDictionaryTerms = (List<DictionaryTerm>)getTermsMethod.invoke(baseObject, (Object[])null);
      if (baseDictionaryTerms != null) {
        for (DictionaryTerm baseDictionaryTerm : baseDictionaryTerms) {
          baseDictionaryTermsValues.add(baseDictionaryTerm.getValue());
        }
      }
      currentDictionaryTerms = (List<DictionaryTerm>)getTermsMethod.invoke(currentObject, (Object[])null);
      if (currentDictionaryTerms != null) {
        for (DictionaryTerm currentDictionaryTerm : currentDictionaryTerms) {
          currentDictionaryTermsValues.add(currentDictionaryTerm.getValue());
        }
      }
    }
    log.debug("XML-267 Creating new mergeAttributes object");
    Attributes mergeAttributes = new Attributes();
    if (currentAttributes != null && !currentAttributes.isEmpty()) {
      log.debug("XML-268 Iterating the Attributes map");
      Iterator<Map.Entry<String, Object>> itAttr = currentAttributes.entrySet().iterator();
      while (itAttr.hasNext()) {
        Object oldValue;
        Map.Entry<String, Object> newPair = itAttr.next();
        String keyName = newPair.getKey();
        Object newValue = newPair.getValue();
        if(newValue!=null) {
          log.debug("XML-270 Reviewing "+keyName+" newValue="+newValue.toString());
        }
        else {
          log.debug("XML-271 Reviewing "+keyName+" newValue=null");
        }
        if (baseAttributes == null) {
          oldValue = null;
        }
        else {
          oldValue = baseAttributes.get(keyName);
          if(oldValue!=null) {
            log.debug("XML-272 Old Value "+keyName+" oldValue="+oldValue.toString());
          }
          else {
            log.debug("XML-273 Old Value "+keyName+" oldValue=null");
          }
        }
        if(newValue==null && oldValue==null) {
          continue;
        }
        mergeAttributes = (Attributes)buildMergeMap((Map<String, Object>)mergeAttributes, keyName, oldValue, newValue);
      }
    }
    
    log.debug("XML-274 Processing objectAttributes");
    List<ObjectAttribute> mergeObjectAttributes = new ArrayList<>();
    Map<String, Object> mergeObjectAttributesMap = new HashMap<>();
    if (compareObject instanceof sailpoint.object.ObjectConfig && currentObjectAttributesMap != null) {
      Iterator<Map.Entry<String, ObjectAttribute>> itObjAttr = currentObjectAttributesMap.entrySet().iterator();
      while (itObjAttr.hasNext()) {
        Map.Entry<String, ObjectAttribute> newPair = itObjAttr.next();
        String keyName = newPair.getKey();
        Object newValue = newPair.getValue();
        Object oldValue = baseObjectAttributesMap.get(keyName);
        mergeObjectAttributesMap = buildMergeMap(mergeObjectAttributesMap, keyName, oldValue, newValue);
      } 
      for (Map.Entry<String, Object> entry : mergeObjectAttributesMap.entrySet()) {
        mergeObjectAttributes.add((ObjectAttribute)entry.getValue());
      }
    }
    
    log.debug("XML-275 Processing auditAttributes");
    List<AuditConfig.AuditAttribute> mergeAuditAttributes = new ArrayList<>();
    Map<String, Object> mergeAuditAttributesMap = new HashMap<>();
    List<AuditConfig.AuditClass> mergeAuditClasses = new ArrayList<>();
    Map<String, Object> mergeAuditClassesMap = new HashMap<>();
    List<AuditConfig.AuditAction> mergeAuditActions = new ArrayList<>();
    Map<String, Object> mergeAuditActionsMap = new HashMap<>();
    if (compareObject instanceof AuditConfig) {
      if (currentAuditAttributesMap != null) {
        Iterator<Map.Entry<String, AuditConfig.AuditAttribute>> itAudAttr = currentAuditAttributesMap.entrySet().iterator();
        while (itAudAttr.hasNext()) {
          Map.Entry<String, AuditConfig.AuditAttribute> newPair = itAudAttr.next();
          String keyName = newPair.getKey();
          Object newValue = newPair.getValue();
          Object oldValue = baseAuditAttributesMap.get(keyName);
          mergeAuditAttributesMap = buildMergeMap(mergeAuditAttributesMap, keyName, oldValue, newValue);
        } 
        for (Map.Entry<String, Object> entry : mergeAuditAttributesMap.entrySet()) {
          mergeAuditAttributes.add((AuditConfig.AuditAttribute)entry.getValue());
        }
      } 
      if (currentAuditClassesMap != null) {
        Iterator<Map.Entry<String, AuditConfig.AuditClass>> itAudClass = currentAuditClassesMap.entrySet().iterator();
        while (itAudClass.hasNext()) {
          Map.Entry<String, AuditConfig.AuditClass> newPair = itAudClass.next();
          String keyName = newPair.getKey();
          Object newValue = newPair.getValue();
          Object oldValue = baseAuditClassesMap.get(keyName);
          mergeAuditClassesMap = buildMergeMap(mergeAuditClassesMap, keyName, oldValue, newValue);
        } 
        for (Map.Entry<String, Object> entry : mergeAuditClassesMap.entrySet()) {
          mergeAuditClasses.add((AuditConfig.AuditClass)entry.getValue());
        }
      } 
      if (currentAuditActionsMap != null) {
        Iterator<Map.Entry<String, AuditConfig.AuditAction>> itAudAction = currentAuditActionsMap.entrySet().iterator();
        while (itAudAction.hasNext()) {
          Map.Entry<String, AuditConfig.AuditAction> newPair = itAudAction.next();
          String keyName = newPair.getKey();
          Object newValue = newPair.getValue();
          Object oldValue = baseAuditActionsMap.get(keyName);
          mergeAuditActionsMap = buildMergeMap(mergeAuditActionsMap, keyName, oldValue, newValue);
        } 
        for (Map.Entry<String, Object> entry : mergeAuditActionsMap.entrySet()) {
          mergeAuditActions.add((AuditConfig.AuditAction)entry.getValue());
        }
      }
    }
    
    log.debug("XML-276 Processing dictionary terms");
    List<DictionaryTerm> mergeDictionaryTerms = new ArrayList<>();
    if (compareObject instanceof sailpoint.object.Dictionary && currentDictionaryTermsValues != null && !currentDictionaryTermsValues.isEmpty()) {
      for (String currentDictionaryTermValue : currentDictionaryTermsValues) {
        if (currentDictionaryTermValue != null && !baseDictionaryTermsValues.contains(currentDictionaryTermValue)) {
          DictionaryTerm mergeDictionaryTerm = new DictionaryTerm();
          mergeDictionaryTerm.setValue(currentDictionaryTermValue);
          mergeDictionaryTerms.add(mergeDictionaryTerm);
        }
      }
    }
    
    log.debug("XML-277 Creating mergeObject using constructor");
    SailPointObject mergeObject = clazz.getDeclaredConstructor(new Class[0]).newInstance(new Object[0]);
    
    if (compareObject instanceof sailpoint.object.Configuration || compareObject instanceof sailpoint.object.UIConfig) {
      log.debug("XML-278 Setting new attributes");
      Method setAttributesMethod = clazz.getMethod("setAttributes", new Class[] { Attributes.class });
      setAttributesMethod.invoke(mergeObject, new Object[] { mergeAttributes });
    }
    else if (compareObject instanceof sailpoint.object.ObjectConfig) {
      if (!mergeAttributes.isEmpty()) {
        Method setConfigAttributesMethod = clazz.getMethod("setConfigAttributes", new Class[] { Attributes.class });
        setConfigAttributesMethod.invoke(mergeObject, new Object[] { mergeAttributes });
      } 
      if (!mergeObjectAttributes.isEmpty()) {
        Method setObjectAttributesMethod = clazz.getMethod("setObjectAttributes", new Class[] { List.class });
        setObjectAttributesMethod
          .invoke(mergeObject, new Object[] { mergeObjectAttributes });
      }
    }
    else if (compareObject instanceof AuditConfig) {
      if (!mergeAuditAttributes.isEmpty()) {
        Method setAttributesMethod = clazz.getMethod("setAttributes", new Class[] { List.class });
        setAttributesMethod.invoke(mergeObject, new Object[] { mergeAuditAttributes });
      } 
      if (!mergeAuditClasses.isEmpty()) {
        Method setClassesMethod = clazz.getMethod("setClasses", new Class[] { List.class });
        setClassesMethod.invoke(mergeObject, new Object[] { mergeAuditClasses });
      } 
      if (!mergeAuditActions.isEmpty()) {
        Method setActionsMethod = clazz.getMethod("setActions", new Class[] { List.class });
        setActionsMethod.invoke(mergeObject, new Object[] { mergeAuditActions });
      } 
    }
    else if (compareObject instanceof sailpoint.object.Dictionary && 
      !mergeDictionaryTerms.isEmpty()) {
      Method setTermsMethod = clazz.getMethod("setTerms", new Class[] { List.class });
      setTermsMethod.invoke(mergeObject, new Object[] { mergeDictionaryTerms });
    } 
    String objectName = object.getName();
    if (objectName != null) {
      objectName = object.getId();
    }
    mergeObject.setName(objectName);
    mergeXml = mergeObject.toXml();
    mergeXml = mergeXml.replace("<!DOCTYPE " + clazz.getSimpleName(), "<!DOCTYPE sailpoint");
    mergeXml = mergeXml.replace("\"sailpoint.dtd\">", "\"sailpoint.dtd\">\n<sailpoint>\n<ImportAction name=\"merge\">");
    mergeXml = mergeXml + "</ImportAction>\n</sailpoint>";
    return mergeXml;
  }
  
  @SuppressWarnings("unchecked")
  private Map<String, Object> buildMergeMap(Map<String, Object> mergeAttributes, String keyName, Object oldValue, Object newValue) throws GeneralException {
    log.debug("XML-280 Entered buildMergeMap for "+keyName);
    if(oldValue!=null) {
      log.debug("XML-281 buildMergeMap entered for "+keyName+" of type "+oldValue.getClass().getName());
    }
    else {
      mergeAttributes.put(keyName,newValue);
      return mergeAttributes;
    }
    List<Object> list=null;
    Boolean oldEqualsNew = Boolean.valueOf(true);
    if (newValue != null && !(newValue instanceof List) && !(newValue instanceof Map)) {
      log.debug("XML-282 Comparing non-collection object of type "+newValue.getClass().getName()+" values "+oldValue+":"+newValue);
      oldEqualsNew = objectsAreEqual(oldValue, newValue);
      log.debug("XML-283 Compare yields "+oldEqualsNew);
      if(!oldEqualsNew.booleanValue()) {
        mergeAttributes.put(keyName,newValue);
      }
    }
    else if (newValue instanceof Map) {
      log.debug("XML-284 Comparing Map object of type "+newValue.getClass().getName());
      Map<String, Object> newMap = new HashMap<>();
      Iterator<Map.Entry<String, Object>> itMap = ((Map<String, Object>)newValue).entrySet().iterator();
      while (itMap.hasNext()) {
        Map.Entry<String, Object> pairs = itMap.next();
        String key = pairs.getKey();
        Object newVal = pairs.getValue();
        Object oldVal = ((Map)oldValue).get(key);
        if (oldVal == null || (oldVal != null && !objectsAreEqual(oldVal, newVal).booleanValue())) {
          oldEqualsNew = Boolean.valueOf(false);
          newMap.put(key, newVal);
        } 
      } 
      if (!newMap.isEmpty()) {
        oldEqualsNew = Boolean.valueOf(false);
        newValue = newMap;
      }
      log.debug("XML-285 Compare yields "+oldEqualsNew);
      if(!oldEqualsNew.booleanValue()) {
        mergeAttributes.put(keyName,newValue);
      }
    }
    else if (newValue instanceof List) {
      log.debug("XML-286 Comparing List object of type "+newValue.getClass().getName());
      List<String> serializedOldValueList = new ArrayList<String>();
      Boolean listNotSerializable = Boolean.valueOf(false);
      for (Object oldVal : (List<Object>)oldValue) {
        if (oldVal instanceof AbstractXmlObject) {
          AbstractXmlObject oldValAbstract = (AbstractXmlObject)oldVal;
          serializedOldValueList.add(oldValAbstract.toXml());
        }
      }
      List<Object> newItems = new ArrayList();
      for (Object newVal : (List<Object>)newValue) {
        if (newVal instanceof AbstractXmlObject) {
          AbstractXmlObject newValAbstract = (AbstractXmlObject)newVal;
          if (!serializedOldValueList.contains(newValAbstract.toXml())) {
            newItems.add(newVal);
          }
          continue;
        } 
        if (!((List)oldValue).contains(newVal)) {
          newItems.add(newVal);
        }
      } 
      if (!newItems.isEmpty()) {
        oldEqualsNew = Boolean.valueOf(false);
        list = newItems;
      }
      if (listNotSerializable.booleanValue() && oldValue != null && oldValue != list && !oldValue.equals(list)) {
        oldEqualsNew = Boolean.valueOf(false);
      }
      log.debug("XML-287 Compare yields "+oldEqualsNew);
      if(!oldEqualsNew.booleanValue()) {
        log.debug("XML-288 Setting "+keyName+" = "+list);
        mergeAttributes.put(keyName, list);
      }
    }
    //log.debug("Returning "+mergeAttributes);
    return mergeAttributes;
  }
  
  @SuppressWarnings("unchecked")
  private String addCData(String objectName, String xml) {
    log.debug("XML-290 Entered addCData for "+objectName);
    Pattern sourceTagPattern = Pattern.compile("(<Source>.+?</Source>)", 32);
    Matcher sourceMatcher = sourceTagPattern.matcher(xml);
    List<String> codeSegments = new ArrayList<>();
    while (sourceMatcher.find()) {
      String code = sourceMatcher.group(1);
      if (!codeSegments.contains(code)) {
        codeSegments.add(code);
      }
    } 
    for (String codeSegment : codeSegments) {
      String utemp="";
      int cblen=40;
      int celen=40;
      if(codeSegment.length() < 40) {
        cblen=codeSegment.length();
        celen=cblen;
      }
      log.debug("XML-291 Found a code segment starting with "+codeSegment.substring(0,cblen));
      log.debug("XML-292 and ending with "+codeSegment.substring(codeSegment.length()-celen));
      
      String unescaped = StringEscapeUtils.unescapeXml(codeSegment);
      int blen=40;
      int elen=40;
      if(unescaped.length() < 40) {
        blen=unescaped.length();
        elen=blen;
      }
      log.debug("XML-293 Found an unescaped code segment, length "+unescaped.length()+", blen="+blen+", starting with "+unescaped.substring(0,blen));
      log.debug("XML-294 and ending with "+unescaped.substring(unescaped.length()-elen));
      char[] values=unescaped.toCharArray();
      byte firstChar=(byte)values[0];
      byte lastChar=(byte)values[values.length-1];
      if(unescaped.startsWith("<Source>")) {
        utemp=unescaped.substring(8);
        unescaped=utemp;
        blen=blen-8;
        log.debug("XML-295 now unescaped code, length "+unescaped.length()+", blen="+blen+", starts with "+unescaped.substring(0,blen));
        // Check for carriage returns or new lines
        values=unescaped.toCharArray();
        firstChar=(byte)values[0];
        log.debug("XML-295X  first character is "+(byte)values[0]);
        log.debug("XML-295Y second character is "+(byte)values[1]);
        while(firstChar==10 || firstChar==13) {
          utemp=unescaped.substring(1);
          unescaped=utemp;
          values=unescaped.toCharArray();
          firstChar=(byte)values[0];
          blen=blen-1;
          log.debug("XML-295Z  first character is "+(byte)values[0]);
        }
        log.debug("XML-295B now unescaped code, length "+unescaped.length()+", blen="+blen+", starts with "+unescaped.substring(0,blen));
      }
      if(unescaped.length() < 40) {
        elen=unescaped.length();
      }
      if(unescaped.endsWith("</Source>")) {
        int trimto=unescaped.length()-9;
        log.debug("XML-296M unescaped length="+unescaped.length()+", elen="+elen+", trimto = "+trimto);
        utemp=unescaped.substring(0,trimto);
        unescaped=utemp;
        elen=elen-9;
        log.debug("XML-296 now unescaped code, length "+unescaped.length()+", elen="+elen+", ends with "+unescaped.substring(unescaped.length()-elen));
        values=unescaped.toCharArray();
        lastChar=(byte)values[values.length-1];
        log.debug("XML-296X  last character is "+(byte)values[values.length-1]);
        while(lastChar==10 || lastChar==13) {
          unescaped=unescaped.substring(0,(unescaped.length()-1));
          log.debug("XML-296A now unescaped code, length "+unescaped.length()+", elen="+elen+",  ends with "+unescaped.substring(unescaped.length()-elen));
          values=unescaped.toCharArray();
          lastChar=(byte)values[values.length-1];
          elen=elen-1;
          log.debug("XML-296Z  last character is "+(byte)values[values.length-1]);
        }
        log.debug("XML-296D now unescaped code, length "+unescaped.length()+", elen="+elen+", ends with "+unescaped.substring(unescaped.length()-elen));
      }
      int ispace=0;
      String spaces="";
      while (unescaped.charAt(ispace)==' ') {
        ispace++;
        spaces=spaces+" ";
        if(ispace >= unescaped.length()) break;
      }
      log.debug("XML-297 ispace="+ispace);
      xml = xml.replace(codeSegment, "<Source><![CDATA[\r\n" + unescaped + "]]></Source>");
    } 
    Pattern htmlTagPattern = Pattern.compile("&lt;html.*?&gt;(.+?)&lt;/html&gt;", 32);
    Matcher htmlMatcher = htmlTagPattern.matcher(xml);
    List<String> htmlSegments = new ArrayList<>();
    while (htmlMatcher.find()) {
      String html = htmlMatcher.group(0);
      if (!htmlSegments.contains(html))
        htmlSegments.add(html); 
    } 
    for (String htmlSegment : htmlSegments) {
      // KCS 2023-09-06 removing cr because the html does not line up
      // and the <html> looks better right after the cdata
      xml = xml.replace(htmlSegment, "<![CDATA[" + 
          StringEscapeUtils.unescapeXml(htmlSegment) + "]]>");
    }          
    Pattern soapMessagePattern = Pattern.compile("<entry key=\"soapMessage\"(.+?)/>", 32);
    Matcher soapMessageMatcher = soapMessagePattern.matcher(xml);
    while (soapMessageMatcher.find()) {
      String entry = soapMessageMatcher.group(0);
      String modifiedEntry = entry.replace("<entry key=\"soapMessage\" value=\"", "");
      modifiedEntry = modifiedEntry.replace("\"/>", "");
      modifiedEntry = "<entry key=\"soapMessage\"> <value> <String><![CDATA[" + StringEscapeUtils.unescapeXml(modifiedEntry) + "]]></String> </value> </entry>";
      xml = xml.replace(entry, modifiedEntry);
    } 
    return xml;
  }
  
  @SuppressWarnings("unchecked")
  private Boolean objectsAreEqual(Object oldObject, Object newObject) throws GeneralException {
    if(oldObject==null && newObject==null) {
      log.debug("XML-300 Entered objectsAreEqual with two null values, returning true");
      return Boolean.valueOf(true);
    }
    else if(oldObject==null) {
      log.debug("XML-301 Entered objectsAreEqual with old=null and new ["+newObject.getClass().getName()+"]");
      return Boolean.valueOf(false);
    }
    else if(newObject==null) {
      log.debug("XML-302 Entered objectsAreEqual with new=null and old ["+oldObject.getClass().getName()+"]");
      return Boolean.valueOf(false);
    }
    log.debug("XML-303 Entered objectsAreEqual with two "+oldObject.getClass().getName());
    if (oldObject instanceof AbstractXmlObject) {
      if (!((AbstractXmlObject)oldObject).toXml().equals(((AbstractXmlObject)newObject).toXml())) {
        return Boolean.valueOf(false);
      }
    } 
    else if (!String.valueOf(newObject).equals(String.valueOf(oldObject))) {
      return Boolean.valueOf(false);
    } 
    return Boolean.valueOf(true);
  }
  
  @SuppressWarnings("unchecked")
  private static String documentAsString(Document doc) {
    DOMSource domSource = new DOMSource(doc);
    StringWriter writer = new StringWriter();
    StreamResult result = new StreamResult(writer);
    TransformerFactory tf = TransformerFactory.newInstance();
    try {
      Transformer transformer = tf.newTransformer();
      transformer.setOutputProperty("indent", "yes");
      DocumentType doctype = doc.getDoctype();
      if (doctype != null) {
        transformer.setOutputProperty("doctype-public", doctype.getPublicId());
        transformer.setOutputProperty("doctype-system", doctype.getSystemId());
      } 
      System.setProperty("line.separator", "\n");
      transformer.transform(domSource, result);
      return writer.toString();
    }
    catch (TransformerConfigurationException e) {
      log.error("XML-310 In documentAsString got "+e.getClass().getName()+":"+e.getMessage());
      e.printStackTrace();
    }
    catch (IllegalArgumentException e) {
      log.error("XML-311 In documentAsString got "+e.getClass().getName()+":"+e.getMessage());
      e.printStackTrace();
    }
    catch (TransformerException e) {
      log.error("XML-312 In documentAsString got "+e.getClass().getName()+":"+e.getMessage());
      e.printStackTrace();
    } 
    return null;
  }
  
  @SuppressWarnings("unchecked")
  public static String doReverseSubstitution(String xml, String revTargetFilePath) throws IOException {
    File f = new File(revTargetFilePath);
    Properties props = new Properties();
    String xpathExpr = null;
    String xpathValue = null;
    String xpathExprMod = null;
    if (f.exists()) {
      FileInputStream fio=new FileInputStream(revTargetFilePath);
      props.load(fio);
      fio.close();
    }
    try {
      log.debug("Creating Document for XPath work");
      
      XPathFactory xPathfactory = XPathFactory.newInstance();
      DocumentBuilderFactory dbfact = DocumentBuilderFactory.newInstance();
      dbfact.setAttribute("http://apache.org/xml/features/nonvalidating/load-external-dtd", Boolean.valueOf(false));
      DocumentBuilder builder = dbfact.newDocumentBuilder();
      log.debug("XML-321 DocumentBuilder instance created");
      InputSource is = new InputSource();
      is.setCharacterStream(new StringReader(xml));
      Document indexname_input = builder.parse(is);
      log.debug("XML-322 indexname_input Document created");
      indexname_input.setXmlStandalone(true);
      log.debug("XML-323 xmlDocument created, creating XPath instance");
      XPath xpath = xPathfactory.newXPath();
      log.debug("XML-324 XPath instance instance created, iterating tokenMap");
      Set<Node> deleteNodes=new HashSet<Node>();
      for (Object xp : props.keySet()) {
        if(xp != null && xp instanceof String) {
          xpathExpr = (String)xp;
          log.trace("XML-325 xpathExpr = "+xpathExpr);
          xpathValue = props.getProperty((String)xp);
          log.trace("XML-326 xpathValue = "+xpathValue);
          if(xpathValue!=null) {
            if(!xpathValue.startsWith("%%")) {
              log.warn("XML-327 Found a bad xpath expression"+"\nxpathExpr="+xpathExpr+"\nxpathValue="+xpathValue);
              continue;
            }
          }
          log.trace("XML-328 Checking for token value " + xpathExpr);
          xpathExprMod=xpathExpr.replace("\\", "");
          log.trace("XML-329 Modified token value " + xpathExprMod + ", compiling");
          Object nresult=(NodeList) xpath.compile(xpathExprMod).evaluate(indexname_input, XPathConstants.NODESET);
          if(nresult!=null) {
            if((nresult instanceof NodeList)) {
              log.trace("XML-330 Result is a NodeList, iterating nodes");
              NodeList nodeList = (NodeList)nresult;
              int nllLen=nodeList.getLength();
              log.trace("XML-340 nodeList length is "+nllLen);
              /*
               * Inserted 2023-11-13 so I can clear an attribute
               */
              if(nllLen==0) {
                log.trace("XML-390 Found a element with no nodes, it's an attribute:");
              }
              else {
                for(int inode=0;inode<nllLen;inode++) {
                  Node node = nodeList.item(inode);
                  log.trace("XML-336 inode="+inode+" type="+node.getNodeType()+" checking xpathValue of "+xpathValue);
                  if("%%CLEAR_NODE%%".equals(xpathValue)) {
                    log.debug("XML-337 found CLEAR_NODE, attempting to clear node");
                    //node.getParentNode().removeChild(node);
                    //deleteNodes.add(node);
                    //while (node.hasChildNodes())node.removeChild(node.getFirstChild());
                    if (node.getNodeType() == 1) {
                      Text neuContent = node.getOwnerDocument().createTextNode("");
                      while (node.hasChildNodes())node.removeChild(node.getFirstChild());
                      node.appendChild(neuContent);
                    }
                    else {
                      Element parentNode=((Attr)node).getOwnerElement();
                      parentNode.removeAttributeNode((Attr)node);
                    }
                  }
                  if("%%REMOVE_NODE%%".equals(xpathValue)) {
                    log.debug("XML-337 found REMOVE_NODE, attempting to remove node");
                    //node.getParentNode().removeChild(node);
                    //deleteNodes.add(node);
                    //while (node.hasChildNodes())node.removeChild(node.getFirstChild());
                    if (node.getNodeType() == 1) {
                      //Text neuContent = node.getOwnerDocument().createTextNode("");
                      while (node.hasChildNodes())node.removeChild(node.getFirstChild());
                      //node.appendChild(neuContent);
                      Node pnode=node.getParentNode();
                      if(pnode!=null) {
                        pnode.getParentNode().removeChild(pnode);
                      }
                    }
                    else {
                      Element parentNode=((Attr)node).getOwnerElement();
                      parentNode.removeAttributeNode((Attr)node);
                      Node dparent=((Node)parentNode).getParentNode();
                      dparent.removeChild((Node)parentNode);
                      //node.setNodeValue("");
                    }
                  }
//                  else if(xpathValue.equals("%%REMOVE_PARENT%%")) {
//                    log.debug("XML-338 found REMOVE_PARENT, attempting to remove parent node");
//                    Node parentNode=node.getParentNode();
//                    parentNode.getParentNode().removeChild(parentNode);
//                  }
                  else {
                    if (node.getNodeType() == 1) {
                      Text neuContent = node.getOwnerDocument().createTextNode(xpathValue);
                      while (node.hasChildNodes())node.removeChild(node.getFirstChild());
                      node.appendChild(neuContent);
                    }
                    else {
                      node.setNodeValue(xpathValue);
                    }
                  }
                }
              }
            }
            else {
              log.debug("XML-331 The nresult object is a "+nresult.getClass().getName());
            }
          }
          else {
            log.trace("XML-332 nresult is null");
          }
        }
      }
      /*
      if(!deleteNodes.isEmpty()) {
        for(Node node: deleteNodes) {
          short nodeType=node.getNodeType();
          Node parentNode=null;
          if(org.w3c.dom.Node.ATTRIBUTE_NODE==nodeType) {
            log.trace("XML-341 this is an Attr");
            parentNode=((Attr)node).getOwnerElement();
          }
          else {
            parentNode=node.getParentNode();
          }
          if(parentNode!=null) {
            log.debug("XML-338 Removing node");
            parentNode.removeChild(node);
          }
          else {
            log.debug("XML-339 parentNode is null, not doing it");
          }
        }
      }
      */
      TransformerFactory transformerFactory = TransformerFactory.newInstance();
      Transformer transformer = transformerFactory.newTransformer();
      transformer.setOutputProperty(OutputKeys.INDENT,"yes");
      transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount","2");
      DocumentType doctype = indexname_input.getDoctype();
      if (doctype != null) {
        transformer.setOutputProperty("doctype-public", doctype.getPublicId());
        transformer.setOutputProperty("doctype-system", doctype.getSystemId());
      }
      DOMSource dsource=new DOMSource(indexname_input);
      StreamResult sresult=new StreamResult(new StringWriter());
      transformer.transform(dsource,sresult);
      return sresult.getWriter().toString();
    }
    catch (XPathExpressionException|javax.xml.parsers.ParserConfigurationException e) {
      log.error("XML-333 In doReverseSubstitution got "+e.getClass().getName()+":"+e.getMessage());
      e.printStackTrace();
    } 
    catch (SAXException e) {
      log.error("XML-334 In doReverseSubstitution got "+e.getClass().getName()+":"+e.getMessage());
      e.printStackTrace();
    }
    catch (Exception e) {
      log.error("XML-335 In doReverseSubstitution got "+e.getClass().getName()+":"+e.getMessage());
      e.printStackTrace();
    }
    return null;
  }
  
  @SuppressWarnings("unchecked")
  public static String getIIQDAName(String objectType, String objectName) {
    String iiqDAName = objectType + "-" + toCamelCase(objectName);
    iiqDAName = iiqDAName.replace(":", "_");
    iiqDAName = iiqDAName.replaceAll("[^a-zA-Z0-9_.-]", "");
    return iiqDAName;
  }
  
  @SuppressWarnings("unchecked")
  public static String getModIIQDAName(String objectType, String objectName) {
    String iiqDAName = null;
    // If there is a dash in the name, keep the capitalization the same
    if(objectName.contains("-")) {
      iiqDAName = objectType+"-"+objectName;
    }
    else {
      iiqDAName = objectType + "-" + toCamelCase(objectName);
    }
    iiqDAName = iiqDAName.replace(":", "_");
    iiqDAName = iiqDAName.replaceAll("[^a-zA-Z0-9_.-]", "");
    return iiqDAName;
  }
  
  @SuppressWarnings("unchecked")
  public static String toCamelCase(String name) {
    if (name == null) {
      return null;
    }
    if (name.equals(name.toUpperCase())) {
      return name;
    }
    StringBuilder camel = new StringBuilder();
    if (name.contains(" ")) {
      String[] words=name.split(" ");
      for (int iw=0; iw<words.length; iw++) {
        String word=words[iw];
        if(word.equals(word.toUpperCase())) {
          camel.append(word);
        }
        else {
          boolean upper = true;
          for (int i = 0; i < word.length(); i++) {
            char c = word.charAt(i);
            if (upper) {
              camel.append(Character.toUpperCase(c));
              upper = false;
            }
            else {
              camel.append(Character.toLowerCase(c));
            }
          }
        }
      }
      return camel.toString();
    }
    return name;
  }
  
  public boolean terminate() {
    terminate = true;
    taskResult.setTerminated(true);
    if (log.isDebugEnabled())
      log.debug("XML-339 Task was terminated."); 
    return true;
  }
  
  public String getPluginName() {
    return PLUGIN_NAME;
  }
}
