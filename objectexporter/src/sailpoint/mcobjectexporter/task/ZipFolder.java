package sailpoint.mcobjectexporter.task;

import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.Calendar;
import java.util.Set;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.Stack;
import java.util.zip.*;
import java.io.*;
import org.apache.commons.lang.StringEscapeUtils;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.w3c.dom.Document;
import org.w3c.dom.DocumentType;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.w3c.dom.Text;

import sailpoint.api.SailPointContext;
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
import sailpoint.object.SailPointObject;
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
//import javax.xml.parsers.DocumentBuilderFactory;
//import javax.xml.parsers.DocumentBuilder;
//import org.xml.sax.InputSource;
//
//import org.xml.sax.SAXException;
//import javax.xml.transform.Transformer;
//import javax.xml.transform.TransformerConfigurationException;
//import javax.xml.transform.TransformerException;
//import javax.xml.transform.TransformerFactory;
//import javax.xml.transform.OutputKeys;
//import javax.xml.transform.dom.DOMSource;
//import javax.xml.transform.stream.StreamResult;
//import javax.xml.xpath.XPath;
//import javax.xml.xpath.XPathConstants;
//import javax.xml.xpath.XPathExpressionException;
//import javax.xml.xpath.XPathFactory;
//import org.eclipse.core.resources.IFile;
/**
 * Export XML objects from IdentityIQ
 *
 * @author <a href="mailto:paul.wheeler@sailpoint.com">Paul Wheeler</a>
 */
public class ZipFolder extends BasePluginTaskExecutor {
  private static final String PLUGIN_NAME = "MCObjectExporterPlugin";
  
  private static Log log = LogFactory.getLog(ZipFolder.class);
  String _basePath="";
  String _outputPath="";
  String _outputFile="";
  String _outputFileName="";
  boolean _recurse=true;
  boolean _deleteSource=false;
  boolean _appendZip=false;
  boolean fileIsOpen=false;
  boolean terminate=false;
  boolean unixOrigin=false;
  // KCS 2022-03-31 Search Level and Search Age are added to archive older folders
  int _searchLevel=0;
  int _searchAge=0;
  //
  int foldersIncluded=0;
  int filesIncluded=0;
  int folderLevel=0;
  Integer folderLevelInt=null;
  String exportDetails=null;
  FileOutputStream fileOutputStream=null;
  ZipOutputStream zipOutputStream=null;
  Stack<File> zipStack=new Stack<File>();
  int BUFFER_SIZE=1024*8;
  int EOF=-1;
  int OFFSET_START=0;
  int SUBSTRING_OFFSET=1;
  String EMPTY="";
  File basePathObj=null;
  File outputPathObj=null;
  int totalFolders=0;
  int totalFiles=0;
  int grandTotalFiles=0;
  int grandTotalFolders=0;
  long oldestDate=0L;
  StringBuffer sboutput=new StringBuffer();
  
  private TaskResult taskResult;
  @SuppressWarnings({"rawtypes","unchecked"})
  @Override
  public void execute(SailPointContext context, TaskSchedule schedule,
    TaskResult result, Attributes args) throws Exception {
    DateFormat sdfout=new SimpleDateFormat("MM/dd/yyyy HH:mm:ss");
    DateFormat sdfnotime=new SimpleDateFormat("MM/dd/yyyy");
    Date now=new Date();
    Date nowNoTime=now;
    String nowDateNoTimeStr=sdfnotime.format(now);
    try {
      nowNoTime=sdfnotime.parse(nowDateNoTimeStr);
    }
    catch (Exception et) {}
    oldestDate=nowNoTime.getTime();
    sboutput.append("ZipFolder started at "+sdfout.format(now));
    if (log.isDebugEnabled()) {
      log.debug("ZF-001 Starting Zip Folder"); 
    }
    taskResult=result;
    
    _basePath=args.getString("basePath");
    log.debug("ZF-002 Base path: " + _basePath);
    
    _outputPath=args.getString("outputPath");
    log.debug("ZF-003 Output path: " + _outputPath);
    
    _outputFileName=args.getString("outputFile");
    log.debug("ZF-004 Output file: " + _outputFile);
    
    _recurse=args.getBoolean("recurse");
    log.debug("ZF-005 Recurse: " + _recurse);
    
    _deleteSource=args.getBoolean("deleteSource");
    log.debug("ZF-006 Delete Source: " + _deleteSource);
    
    // KCS 2022-03-31 Search Level and Search Age are added to archive older folders
    _searchLevel=args.getInt("searchLevel");
    log.debug("ZF-007 Search Level = "+_searchLevel);
    
    _searchAge=args.getInt("searchAge");
    log.debug("ZF-008 Search Age = "+_searchAge);
    
    _appendZip=args.getBoolean("appendZip");
    log.debug("ZF-009 Append Zip = "+_appendZip);
    
    String folderSep=File.separator;
    if(folderSep.equals("/")) {
      unixOrigin=true;
    }
    log.debug("ZF-010 unixOrigin = "+unixOrigin);
    
    if (!terminate) {
      _basePath=_basePath.replaceAll("\\\\", "/");
      if (!_basePath.endsWith("/")) {
        _basePath=_basePath + "/";
        log.debug("ZF-015 Base path: " + _basePath);
      }
      // KCS 2020-05-08
      if(_basePath.contains("$date$")) {
        DateFormat bpdf=new SimpleDateFormat("yyyyMMdd");
        String nowStr=bpdf.format(now);
        _basePath=_basePath.replace("$date$", nowStr);
        log.debug("ZF-020 Base path: " + _basePath);
      }
      if(_basePath.contains("$datetime$")) {
        DateFormat bpdf=new SimpleDateFormat("yyyyMMdd-HHmm");
        String nowStr=bpdf.format(now);
        _basePath=_basePath.replace("$datetime$", nowStr);
        log.debug("ZF-025 Base path: " + _basePath);
      }
      // Check for existence of basePath
      basePathObj=new File(_basePath);
      if(basePathObj.exists()) {
        log.debug("ZF-030 The basePath "+_basePath+" exists");
      }
      else {
        log.error("ZF-035 Could not find the basePath folder "+_basePath);
        taskResult.setCompletionStatus(TaskResult.CompletionStatus.Error);
        taskResult.addMessage(new Message(Message.Type.Error,"Could not find the basePath folder"));
        return;
      }
    }
    else {
      log.error("ZF-040 Terminate chosen");
      taskResult.setCompletionStatus(TaskResult.CompletionStatus.Warning);
      taskResult.addMessage(new Message(Message.Type.Info,"Cancelled by user input"));
      return;
    }
    sboutput.append("\nbasePath="+_basePath);
    updateProgress(context, result, "Found basePath "+_basePath);
    // Find or create the output file path
    if (!terminate) {
      _outputPath=_outputPath.replaceAll("\\\\", "/");
      log.debug("ZF-045 Output path: " + _outputPath);
      if (!_outputPath.endsWith("/")) {
        _outputPath=_outputPath + "/";
        log.debug("ZF-050 Output path: " + _outputPath);
      }
      // KCS 2020-05-08
      if(_outputPath.contains("$date$")) {
        DateFormat bpdf=new SimpleDateFormat("yyyyMMdd");
        String nowStr=bpdf.format(now);
        _outputPath=_outputPath.replace("$date$", nowStr);
        log.debug("ZF-055 Output path: " + _outputPath);
      }
      if(_outputPath.contains("$datetime$")) {
        DateFormat bpdf=new SimpleDateFormat("yyyyMMdd-HHmm");
        String nowStr=bpdf.format(now);
        _outputPath=_outputPath.replace("$datetime$", nowStr);
        log.debug("ZF-060 Output path: " + _outputPath);
      }
      // Check for existence of basePath
      outputPathObj=new File(_outputPath);
      if(outputPathObj.exists()) {
        log.debug("ZF-065 The outputPath "+_outputPath+" exists");
      }
      else {
        if(outputPathObj.mkdirs()) {
          log.debug("ZF-070 Successfully created "+_outputPath);
        }
        else {
          log.error("ZF-075 Could not create folder "+_outputPath);
          taskResult.setCompletionStatus(TaskResult.CompletionStatus.Error);
          taskResult.addMessage(new Message(Message.Type.Error,"Could not create the output folder"));
          return;
        }
      }
    }
    else {
      log.error("ZF-080 Terminate chosen");
      taskResult.setCompletionStatus(TaskResult.CompletionStatus.Warning);
      taskResult.addMessage(new Message(Message.Type.Info,"Cancelled by user input"));
      return;
    }
    sboutput.append("\noutputPath="+_outputPath);
    updateProgress(context, result, "Found or created outputPath "+_outputPath);
    sboutput.append("\nrecurse="+_recurse+" deleteFolder="+_deleteSource);
    log.debug("ZF-085 outputPath="+_outputPath);
    log.debug("ZF-090 recurse="+_recurse+" deleteFolder="+_deleteSource);
    // Borrows code from ZipHelper
    // Source is the basePathObj
    // Destination is the final file
    Calendar nowCal=Calendar.getInstance();
    nowCal.setTime(new Date(oldestDate));
    nowCal.add(Calendar.DAY_OF_YEAR,1-_searchAge);
    oldestDate=nowCal.getTime().getTime();
    sboutput.append("\nIncluding files updated before "+sdfout.format(new Date(oldestDate)));
    log.debug("ZF-095 Including files updated before "+sdfout.format(new Date(oldestDate)));
    Map<Integer,List<File>> folderMap=new HashMap<Integer,List<File>>();
    List<File> folderList=new ArrayList<File>();
    folderLevelInt=Integer.valueOf(0);
    log.debug("ZF-100 Adding basePathObj to folderList");
    folderList.add(basePathObj);
    log.debug("ZF-105 Adding folderList to folderMap");
    folderMap.put(folderLevelInt,folderList);
    log.debug("ZF-110 checking searchLevel");
    updateProgress(context, result, "Creating folderMap and folderList");
    if(_searchLevel==0) {
      log.debug("ZF-115 searchLevel = 0");
    }
    else {
      log.debug("ZF-120 searchLevel = "+_searchLevel);
      folderLevel=1;
      while(folderLevel <= _searchLevel) {
        log.debug("ZF-125 folderLevel = "+folderLevel);
        folderList=folderMap.get(folderLevelInt);
        folderLevelInt=Integer.valueOf(folderLevel);
        List<File> newList=new ArrayList<File>();
        for(File folder:folderList) {
          File[] files=folder.listFiles();
          for(File item:files) {
            if(item.isDirectory()) {
              log.debug("ZF-130 Adding directory at level "+folderLevel+":"+item.getName());
              newList.add(item);
            }
          }
        }
        log.debug("ZF-135 Saving the folder list for level "+folderLevel);
        folderMap.put(folderLevelInt,newList);
        folderLevel++;
      }
    }
    log.debug("ZF-140 folderMap:");
    for(folderLevel=0; folderLevel<=_searchLevel; ++folderLevel) {
      folderLevelInt=Integer.valueOf(folderLevel);
      folderList=folderMap.get(folderLevelInt);
      for(File item:folderList) {
        log.debug("ZF-145 Level:"+folderLevel+" Folder:"+item.getAbsolutePath());
      }
    }
    folderLevel=_searchLevel;
    folderLevelInt=Integer.valueOf(folderLevel);
    folderList=folderMap.get(folderLevelInt);
    for(File item:folderList) {
      log.debug("ZF-150 building zipStack for "+item.getAbsolutePath());
      updateProgress(context, result, "Analyzing "+item.getAbsolutePath());
      totalFiles=0;
      totalFolders=0;
      zipStack.clear();
      if(Util.isNullOrEmpty(_outputFileName)) {
        // Set the output file to the path
        _outputFile=item.getName();
        log.debug("ZF-155 outputFile is null or empty, using "+_outputFile);
      }
      else {
        _outputFile=_outputFileName;
        log.debug("ZF-160 outputFile is specified, using "+_outputFile);
      }
      if (!terminate) {
        _outputFile=_outputFile.replaceAll("\\\\", "/");
        log.debug("ZF-165 outputFile = "+_outputFile);
        if(!_outputFile.endsWith(".zip")) {
          _outputFile=_outputFile+".zip";
          log.debug("ZF-170 outputFile = "+_outputFile);
        }
        if(_outputFile.contains("$date$")) {
          DateFormat bpdf=new SimpleDateFormat("yyyyMMdd");
          String nowStr=bpdf.format(now);
          _outputFile=_outputFile.replace("$date$", nowStr);
          log.debug("ZF-175 outputFile = "+_outputFile);
        }
        if(_outputFile.contains("$datetime$")) {
          DateFormat bpdf=new SimpleDateFormat("yyyyMMdd-HHmm");
          String nowStr=bpdf.format(now);
          _outputFile=_outputFile.replace("$datetime$", nowStr);
          log.debug("ZF-180 outputFile = "+_outputFile);
        }
        if(_outputFile.contains("$folderName$")) {
          _outputFile=_outputFile.replace("$folderName$",item.getName());
          log.debug("ZF-185 outputFile = "+_outputFile);
        }
      }
      else {
        log.error("ZF-190 Terminate chosen");
        taskResult.setCompletionStatus(TaskResult.CompletionStatus.Warning);
        taskResult.addMessage(new Message(Message.Type.Info,"Cancelled by user input"));
        return;
      }
      sboutput.append("\noutputFile="+_outputFile);
      log.debug("ZF-195 outputFile="+_outputFile);
      if(_recurse) {
        log.debug("ZF-200 Recursing the stack");
        recursivelyAddFilesToStack(item);
      }
      else {
        log.debug("ZF-205 Not recursing the stack");
        addFilesToStack(item);
      }
      try {
        if(totalFiles > 0) {
          updateProgress(context, result, "Zipping "+item.getAbsolutePath());
          sboutput.append("\nCreating zip file for output");
          log.debug("ZF-210 Creating zip file for output");
          // boolean _appendZip=false;
          // boolean fileIsOpen=false;
          if((_appendZip && !fileIsOpen) || (!_appendZip)) {
            log.debug("ZF-215 Creating new file "+_outputPath+_outputFile);
            fileOutputStream=new FileOutputStream(new File(_outputPath+_outputFile));
            zipOutputStream=new ZipOutputStream(fileOutputStream);
            fileIsOpen=true;
          }
          zipOutputStream.setLevel(ZipEntry.DEFLATED);
          sboutput.append("\nAdding files to zip file");
          log.debug("ZF-220 Adding files to zip file");
          zip(item);
          if(!_appendZip) {
            sboutput.append("\nClosing the zip file");
            log.debug("ZF-225 Closing the zip file");
            fileOutputStream.flush();
            fileOutputStream.close();
          }
          if(_deleteSource) {
            updateProgress(context, result, "Deleting "+item.getAbsolutePath());
            sboutput.append("\nDeleting the source folder");
            log.debug("ZF-225 Deleting the source folder contents of "+item.getAbsolutePath());
            deleteFolder(item);
            log.debug("ZF-230 Deleting the source folder:"+item.getAbsolutePath());
            item.delete();
          }
          sboutput.append("\nCompleted");
        }
        else {
          sboutput.append("\nThere were no files found in the folder, exiting");
          log.error("ZF-235 The stack is empty, no files in the path");
        }
      }
      catch (Exception ex) {
        log.error("ZF-240 Error:"+ex.getClass().getName()+":"+ex.getMessage());
      }
      grandTotalFiles+=totalFiles;
      grandTotalFolders+=totalFolders;
    }
    if(_appendZip) {
      sboutput.append("\nClosing the zip file");
      log.debug("ZF-245 Closing the zip file");
      zipOutputStream.close();
      fileOutputStream.flush();
      fileOutputStream.close();
    }
    updateProgress(context, result, "Wrapping up");
    result.setAttribute("foldersIncluded", grandTotalFolders);
    result.setAttribute("filesIncluded", grandTotalFiles);
    result.setAttribute("resultString", sboutput.toString());
    taskResult.setCompletionStatus(TaskResult.CompletionStatus.Success);
    taskResult.addMessage(new Message(Message.Type.Info,"Processed "+grandTotalFolders+" folders, "+grandTotalFiles+" files"));
  }
  
  private void recursivelyAddFilesToStack(File file) {
    log.debug("ZF-300 recursivelyAddFilesToStack("+file.getAbsolutePath()+")");
    if(file.isFile()) {
      log.trace("ZF-310 isFile, checking date");
      if(file.lastModified() < oldestDate) {
        log.trace("ZF-315 lastModified < oldestDate, adding to stack");
        zipStack.add(file);
        totalFiles++;
      }
      else {
        log.trace("ZF-320 lastModified >= oldestDate, skipping");
      }
      return;
    }
    log.trace("ZF-325 assuming is folder, recursing");
    File[] files=file.listFiles();
    totalFolders++;
    if(files==null) {
      log.trace("ZF-330 folder is empty, returning");
      return;
    }
    log.trace("ZF-335 found "+files.length+" files/folders");
    for(File item:files) {
      recursivelyAddFilesToStack(item);
    }
  }
  
  private void addFilesToStack(File file) {
    log.debug("ZF-400 addFilesToStack("+file.getAbsolutePath()+")");
    if(file.isFile()) {
      log.trace("ZF-410 isFile, checking date");
      if(file.lastModified() < oldestDate) {
        log.trace("ZF-415 lastModified < oldestDate, adding to stack");
        zipStack.add(file);
        totalFiles++;
      }
      else {
        log.trace("ZF-420 lastModified >= oldestDate, skipping");
      }
      return;
    }
    log.trace("ZF-425 assuming is folder, recursing");
    File[] files=file.listFiles();
    totalFolders++;
    if(files==null) {
      log.trace("ZF-430 folder is empty, returning");
      return;
    }
    log.trace("ZF-435 found "+files.length+" files/folders");
    for(File item:files) {
      if(item.isFile()) {
        log.debug("ZF-440 addFilesToStack("+item.getAbsolutePath()+")");
        if(item.lastModified() < oldestDate) {
          log.trace("ZF-445 lastModified < oldestDate, adding to stack");
          zipStack.add(item);
          totalFiles++;
        } else {
          log.trace("ZF-450 lastModified >= oldestDate, skipping");
        }
      }
    }
  }
  
  private void deleteFolder(File file) {
    boolean hasWEBINF=false;
    boolean hasDTD=false;
    log.debug("ZF-500 deleteFolder("+file.getAbsolutePath()+")");
    for (File subFile: file.listFiles()) {
      if(subFile.isDirectory()) {
        String folderName=file.getName();
        if("WEB-INF".equals(folderName)) hasWEBINF=true;
      }
      else {
        String fileName=file.getName();
        if(Util.isNotNullOrEmpty(fileName)) {
          fileName=fileName.toLowerCase();
          if(fileName.startsWith("sailpoint")) {
            if(fileName.endsWith("dtd")) {
              hasDTD=true;
            }
          }
        }
      }
    }
    if(hasWEBINF && hasDTD) {
      log.error("ZF-505 ZipFolder is designed to not delete sailpoint main folders");
      return;
    }
    for (File subFile: file.listFiles()) {
      log.trace("ZF-505 deleting "+subFile.getAbsolutePath());
      if(subFile.isDirectory()) {
        deleteFolder(subFile);
        File[] remainingFiles=subFile.listFiles();
        if(remainingFiles.length==0) {
          subFile.delete();
        }
      }
      else {
        if(subFile.lastModified() < oldestDate) {
          subFile.delete();
        }
      }
    }
  }

  private void zip(File folder) throws IOException {
    while(true) {
      if(zipStack.empty()) {
        if(!_appendZip) {
          zipOutputStream.close();
        }
        break;
      }
      zipFile(zipStack.pop(),folder);
    }
  }
  private void zipFile(File file, File folder) throws IOException {
    String relativePath=file.getAbsolutePath().replace(folder.getAbsolutePath(),EMPTY);
    if(relativePath.isEmpty()) {
      relativePath=folder.getName();
    }
    else {
      relativePath=relativePath.substring(SUBSTRING_OFFSET);
    }
    ZipEntry zipEntry=new ZipEntry(relativePath);
    zipOutputStream.putNextEntry(zipEntry);
    final FileInputStream fileInputStream=new FileInputStream(file);
    final byte[] buffer=new byte[BUFFER_SIZE];
    int readBytes=0;
    while (true) {
      readBytes=fileInputStream.read(buffer);
      if(readBytes == EOF) break;
      zipOutputStream.write(buffer,OFFSET_START, readBytes);
    }
    fileInputStream.close();
    zipOutputStream.closeEntry();
  }
  
  public boolean terminate() {
    terminate=true;
    taskResult.setTerminated(true);
    if (log.isDebugEnabled())
      log.debug("Task was terminated."); 
    return true;
  }
  
  public String getPluginName() {
    return PLUGIN_NAME;
  }
}
