package edu.nyu.cascade.util;

import java.util.Map;
import java.util.Map.Entry;

import org.apache.commons.lang.time.StopWatch;

import com.google.common.collect.Maps;

public class StatsTimer {
	private static Map<String, StopWatch> statsMap = Maps.newLinkedHashMap();
	private static StopWatch cascadeWatch;
	
	private static StopWatch register(String methodName) {
		StopWatch stopWatch = new StopWatch();
		statsMap.put(methodName, stopWatch);
		return stopWatch;
	}
	
	private static String getKeyName(StackTraceElement elem) {
		String className = elem.getClassName();
		int index = className.lastIndexOf('.');
		className = className.substring(index+1);
		String methodName = elem.getMethodName();
		return className + ':' + methodName;
	}
	
	public static void cascadeStart() {
		cascadeWatch = new StopWatch();
		cascadeWatch.start();
	}
	
	public static void cascadeStop() {
		cascadeWatch.stop();
	}
	
	public static long cascadeElapseTime() {
		return cascadeWatch.getTime();
	}
	
	public static void start() {
		if(!IOUtils.statsEnabled()) return;
		StackTraceElement[] elems = Thread.currentThread().getStackTrace();
		String keyName = getKeyName(elems[2]);
		
		for(int i = 3; i < elems.length-2; i++) {
			String _keyName = getKeyName(elems[i]);
			if(_keyName.equals(keyName)) continue;
			if(statsMap.containsKey(_keyName)) {
				statsMap.get(_keyName).suspend(); break;
			}
		}
		
		if(!statsMap.containsKey(keyName)) {
			StopWatch stopWatch = register(keyName);
			stopWatch.start();
		} else {
			StopWatch stopWatch = statsMap.get(keyName);
			stopWatch.resume();
		}
	}
	
	public static void suspend() {
		if(!IOUtils.statsEnabled()) return;
		StackTraceElement[] elems = Thread.currentThread().getStackTrace();
		StackTraceElement elem = elems[2];
		String keyName = getKeyName(elem);
		
		for(int i = 3; i < elems.length-2; i++) {
			String _keyName = getKeyName(elems[i]);
			if(_keyName.equals(keyName)) continue;
			if(statsMap.containsKey(_keyName)) {
				statsMap.get(_keyName).resume(); break; 
			}
		}
		
		StopWatch stopWatch = statsMap.get(keyName);
		stopWatch.suspend();
	}
	
	public static String getStatsInfo() {
		StringBuilder sb = new StringBuilder();
	
		for(Entry<String, StopWatch> entry : statsMap.entrySet()) {
			sb.append(entry.getKey())
				.append(' ')
				.append(entry.getValue().getTime()/1000.0).append('s')
				.append('\n');
		}
		return sb.toString();
	}
	
	public static void reset() {
		if(!IOUtils.statsEnabled()) return;
		IOUtils.statsStream().append(getStatsInfo()).append('\n');
		statsMap.clear();
	}
 } 
