package com.android.testtool;


import java.io.Serializable;

public class VideoBufferInfo implements Serializable
{
	public byte[] buffer;
	public int size;
	public long timestamp;
	public int flag;
}